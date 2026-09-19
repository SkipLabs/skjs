"""Reference integration of alias expansion and T[number] with the R2/R3c broker.

This is an executable specification of the first SKJS migration, NOT SKJS's
implementation. Array/tuple shapes are used only for read projections; this
module establishes no mutable-storage subtyping or source-language theorem.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from itertools import count

from model import (
    BOTTOM, Blocked, Invalid, Misuse, Owner, Query, Receipt, Snapshot, Ty,
    included, join,
)


def array(element: Ty) -> Ty:
    return Ty("array", (element,))


def parameter(index: int) -> Ty:
    """A bound alias placeholder, not an inference variable or a skolem."""
    return Ty("bound", label=index)


def alias(identity: str, *arguments: Ty) -> Ty:
    """identity is already resolved; it is not the source spelling."""
    return Ty("alias", arguments, identity)


@dataclass(frozen=True)
class Definition:
    identity: str
    arity: int
    body: Ty


@dataclass(frozen=True)
class Catalog:
    """Immutable semantic input, captured in every judgment descriptor."""
    definitions: tuple[Definition, ...] = ()

    def __post_init__(self) -> None:
        ids = [d.identity for d in self.definitions]
        if len(ids) != len(set(ids)) or any(d.arity < 0 for d in self.definitions):
            raise ValueError("duplicate declaration identity or invalid arity")

    def expand(self, t: Ty) -> Ty:
        if t.op != "alias":
            raise Blocked("expected a resolved alias reference")
        definition = next((d for d in self.definitions if d.identity == t.label), None)
        if definition is None or len(t.args) != definition.arity:
            raise Blocked("unknown declaration identity or wrong alias arity")

        def substitute(body: Ty) -> Ty:
            if body.op == "bound":
                i = body.label
                if not isinstance(i, int) or not 0 <= i < len(t.args):
                    raise Blocked("unbound alias placeholder")
                return t.args[i]
            args = tuple(substitute(a) for a in body.args)
            return join(*args) if body.op == "union" else Ty(body.op, args, body.label)

        return substitute(definition.body)


def _binding(t: Ty, s: Snapshot) -> Ty | None:
    if not isinstance(t.label, int) or t.label not in s.allocated:
        raise Blocked("private, rolled-back, or foreign candidate")
    binding = dict(s.bindings).get(t.label)
    return None if binding is None else binding.value


def _step(fuel: int) -> int:
    if fuel <= 0:
        raise Blocked("recursive or excessively deep normalization is outside this slice")
    return fuel - 1


def well_formed(t: Ty, s: Snapshot, env: Catalog,
                trail: frozenset[int] = frozenset(), fuel: int = 128) -> None:
    """Scope/finite-graph check. Unbound element candidates may stay symbolic."""
    fuel = _step(fuel)
    if t.op == "alias":
        # Check arguments as well as the expansion: an erased private ID is
        # still not a source type in this owner's scope.
        for a in t.args:
            well_formed(a, s, env, trail, fuel)
        well_formed(env.expand(t), s, env, trail, fuel)
        return
    if t.op == "var":
        if t.label in trail:
            raise Blocked("recursive candidate graph")
        value = _binding(t, s)
        if value is not None:
            well_formed(value, s, env, trail | {t.label}, fuel)
        return
    if t.op not in ("atom", "tuple", "array", "record", "field", "union", "element"):
        raise Blocked(f"unsupported type syntax: {t.op}")
    if t.op in ("array", "field", "element") and len(t.args) != 1:
        raise Blocked("wrong operator arity")
    for a in t.args:
        well_formed(a, s, env, trail, fuel)


def element(t: Ty, s: Snapshot, env: Catalog,
            trail: frozenset[int] = frozenset(), fuel: int = 128) -> Ty:
    """Read only the outer shape. Preserve symbolic element identities."""
    fuel = _step(fuel)
    if t.op == "alias":
        return element(env.expand(t), s, env, trail, fuel)
    if t.op == "var":
        if t.label in trail:
            raise Blocked("recursive candidate shape")
        value = _binding(t, s)
        if value is None:
            raise Blocked("an unbound outer shape cannot be guessed")
        return element(value, s, env, trail | {t.label}, fuel)
    if t.op == "element" and len(t.args) == 1:
        return element(element(t.args[0], s, env, trail, fuel), s, env, trail, fuel)
    if t.op == "array" and len(t.args) == 1:
        return t.args[0]
    if t.op == "tuple":
        return join(*t.args)
    if t.op == "union":
        # Every arm must have an established shape. Do not silently discard a
        # bad arm, even if another arm already supplies a useful element type.
        return join(*(element(a, s, env, trail, fuel) for a in t.args))
    raise Blocked("numeric projection requires a known array/tuple shape")


def evaluate(t: Ty, s: Snapshot, env: Catalog,
             trail: frozenset[int] = frozenset(), fuel: int = 128) -> Ty:
    """Fully materialize in an immutable snapshot; never solve or seal."""
    fuel = _step(fuel)
    if t.op == "alias":
        return evaluate(env.expand(t), s, env, trail, fuel)
    if t.op == "var":
        if t.label in trail:
            raise Blocked("recursive candidate value")
        value = _binding(t, s)
        if value is None:
            raise Blocked("an unbound element is not inferred never")
        return evaluate(value, s, env, trail | {t.label}, fuel)
    if t.op == "element" and len(t.args) == 1:
        return evaluate(element(t.args[0], s, env, trail, fuel), s, env, trail, fuel)
    if t.op == "atom":
        return t
    if t.op in ("array", "tuple", "union", "record", "field"):
        args = tuple(evaluate(a, s, env, trail, fuel) for a in t.args)
        return join(*args) if t.op == "union" else Ty(t.op, args, t.label)
    raise Blocked(f"unsupported materialization: {t.op}")


@dataclass(frozen=True)
class ShapeQuery(Query):
    catalog: Catalog

    def holds(self, s: Snapshot) -> bool:
        well_formed(self.source, s, self.catalog)
        well_formed(self.target, s, self.catalog)
        if self.op == "source":
            return self.source == self.target
        if self.op == "expandable":
            self.catalog.expand(self.source)
            return True
        if self.op == "alias":
            return self.catalog.expand(self.source) == self.target
        if self.op in ("indexed_ready", "indexed"):
            if self.source.op != "element" or len(self.source.args) != 1:
                raise Blocked("expected a numeric indexed type expression")
            image = element(self.source.args[0], s, self.catalog)
            if self.op == "indexed_ready" or image == self.target:
                return True
            return evaluate(image, s, self.catalog) == evaluate(self.target, s, self.catalog)
        if self.op == "projectable":
            element(self.source, s, self.catalog)
            return True
        if self.op == "defined":
            evaluate(self.source, s, self.catalog)
            return True
        if self.op == "projection":
            image = element(self.source, s, self.catalog)
            # This equality can be uniform in unbound element candidates.
            if image == self.target:
                return True
            return evaluate(image, s, self.catalog) == evaluate(self.target, s, self.catalog)
        a = evaluate(self.source, s, self.catalog)
        b = evaluate(self.target, s, self.catalog)
        if self.op == "equal":
            return a == b
        if self.op == "sub":
            # The original finite scalar/immutable-structure relation; no
            # additional mutable-array subtyping rule is introduced here.
            return included(a, b)
        raise Blocked(f"unsupported shape judgment: {self.op}")


@dataclass(frozen=True)
class Derived:
    """Opaque handle. Its value and prerequisites live together in the broker."""
    _identity: int
    _issuer: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class _Entry:
    value: Ty
    prerequisites: tuple[tuple[Receipt, Query], ...]


@dataclass(frozen=True)
class ProjectionProposal:
    parent: int
    scope: int
    catalog: Catalog
    original: Ty
    preview: str  # Display only: not a type or receipt to import.


class ProjectionPipeline:
    """Alias -> projection/cache -> subtype consumer -> owner publication.

    No public operation returns an unguarded acceptance-relevant Ty. As in
    model.py, Python underscores stand in for enforced module privacy.
    """
    def __init__(self, owner: Owner, catalog: Catalog = Catalog()) -> None:
        self._owner, self._catalog = owner, catalog
        self._issuer, self._ids = object(), count(1)
        self._entries: dict[int, _Entry] = {}
        self._cache: dict[tuple[str, Ty], Derived] = {}
        self.cache_hits = 0

    @property
    def owner(self) -> Owner:
        return self._owner

    @property
    def catalog(self) -> Catalog:
        return self._catalog

    def _query(self, op: str, a: Ty, b: Ty = BOTTOM) -> ShapeQuery:
        return ShapeQuery(op, a, b, self.catalog)

    def _issue(self, value: Ty, prerequisites: tuple[tuple[Receipt, Query], ...]) -> Derived:
        identity = next(self._ids)
        self._entries[identity] = _Entry(value, prerequisites)
        return Derived(identity, self._issuer)

    def _entry(self, handle: Derived) -> _Entry:
        if not isinstance(handle, Derived) or handle._issuer is not self._issuer:
            raise Misuse("not this pipeline's derived result")
        entry = self._entries.get(handle._identity)
        if entry is None:
            raise Misuse("unknown derived result")
        for receipt, judgment in entry.prerequisites:
            self.owner.use(receipt, judgment)
        return entry

    def source(self, source: Ty) -> Derived:
        q = self._query("source", source, source)
        r = self.owner.require(q)
        return self._issue(source, ((r, q),))

    def _derive(self, op: str, value: Derived) -> Derived:
        entry = self._entry(value)
        key = op, entry.value
        cached = self._cache.get(key)
        if cached is not None:
            try:
                self._entry(cached)
            except Misuse:
                # Entries outside the transactional journal can outlive a
                # discarded alternative. They must not resurrect its receipts.
                del self._cache[key]
            else:
                self.cache_hits += 1
                # The same value can arrive through a different derivation.
                # Its prerequisites still need to be retained (see tests).
                previous = self._entries[cached._identity]
                merged = tuple(dict.fromkeys(previous.prerequisites + entry.prerequisites))
                return cached if merged == previous.prerequisites else self._issue(previous.value, merged)

        # Required request is registered BEFORE computation. Catching Blocked
        # cannot silently turn a failed materialization into accepted source.
        requests = {"projection": "projectable", "indexed": "indexed_ready",
                    "alias": "expandable", "equal": "defined"}
        if op not in requests:
            raise Misuse("invalid internal derivation kind")
        request = self._query(requests[op], entry.value)
        requested = self.owner.require(request)
        if op == "projection":
            result = element(entry.value, self.owner.snapshot, self.catalog)
        elif op == "indexed":
            result = element(entry.value.args[0], self.owner.snapshot, self.catalog)
        elif op == "equal":
            result = evaluate(entry.value, self.owner.snapshot, self.catalog)
        else:
            # Pure binder substitution; don't demand fully solved arguments.
            result = self.catalog.expand(entry.value)
        q = self._query(op, entry.value, result)
        receipt = self.owner.require(q)
        out = self._issue(result, entry.prerequisites + ((requested, request), (receipt, q)))
        self._cache[key] = out
        return out

    def expand(self, value: Derived) -> Derived:
        return self._derive("alias", value)

    def project(self, value: Derived) -> Derived:
        return self._derive("projection", value)

    def materialize(self, value: Derived) -> Derived:
        return self._derive("equal", value)

    def reduce_indexed(self, value: Derived) -> Derived:
        return self._derive("indexed", value)

    def instantiate(self, value: Derived) -> Derived:
        # This slice only handles a leading chain of aliases and one indexed
        # expression; nested structural normalizers are deliberately separate.
        for _ in range(128):
            ty = self._entry(value).value
            if ty.op == "alias":
                value = self.expand(value)
            elif ty.op == "element":
                return self.reduce_indexed(value)
            else:
                return value
        raise Blocked("alias chain exceeds the reference fragment's fuel")

    def combine(self, *values: Derived) -> Derived:
        entries = [self._entry(v) for v in values]
        return self._issue(join(*(e.value for e in entries)),
                           tuple(p for e in entries for p in e.prerequisites))

    def require_subtype(self, source: Derived, target: Derived) -> Receipt:
        a, b = self._entry(source), self._entry(target)
        return self.owner.require(self._query("sub", a.value, b.value))

    def display(self, value: Derived) -> str:
        return repr(self._entry(value).value)

    def probe(self, source: Ty, infer=lambda _: None) -> ProjectionProposal:
        child = self.owner._fork()
        infer(child)
        pipe = ProjectionPipeline(child, self.catalog)
        try:
            preview = pipe.display(pipe.project(pipe.source(source)))
        except (Blocked, Invalid) as error:
            preview = f"blocked: {error}"
        return ProjectionProposal(self.owner.snapshot.owner, self.owner.snapshot.scope,
                                  self.catalog, source, preview)

    def replay(self, proposal: ProjectionProposal) -> Derived:
        if not isinstance(proposal, ProjectionProposal) or (
            proposal.parent != self.owner.snapshot.owner
            or proposal.scope != self.owner.snapshot.scope
            or proposal.catalog != self.catalog
        ):
            raise Misuse("foreign projection proposal")
        # Never import a child's materialized answer or constraints.
        return self.project(self.source(proposal.original))

    def close(self):
        return self.owner.close()
