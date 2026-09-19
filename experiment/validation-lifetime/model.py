"""Executable R2/R3c lifetime protocol, not an SKJS type checker.

Immutable scalar/tuple/record types make the state protocol independently testable.
Recursive types, mutable heap typing, and generic quantification are out of scope.
Private attributes model module boundaries, not protection against Python reflection.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from itertools import count
from typing import Callable

_ids = count(1)  # Session-wide freshness: never saved, restored, or copied.
_issuer = object()


class Blocked(Exception):
    """Unsolved or unsupported: never a successful validation."""


class Invalid(Exception):
    """An active obligation does not hold in the current snapshot."""


class Misuse(Exception):
    """Evidence crossed an ownership, scope, or transaction boundary."""


@dataclass(frozen=True)
class Ty:
    op: str
    args: tuple[Ty, ...] = ()
    label: str | int | None = None


def atom(name: str) -> Ty:
    return Ty("atom", label=name)


def tup(*items: Ty) -> Ty:
    return Ty("tuple", items)


def record(**fields: Ty) -> Ty:
    return Ty("record", tuple(Ty("field", (v,), k) for k, v in sorted(fields.items())))


def join(*items: Ty) -> Ty:
    flat: set[Ty] = set()
    for item in items:
        flat.update(item.args if item.op == "union" else (item,))
    ordered = tuple(sorted(flat, key=repr))
    return ordered[0] if len(ordered) == 1 else Ty("union", ordered)


NUMBER, STRING = atom("number"), atom("string")
BOTTOM = join()


@dataclass(frozen=True)
class Binding:
    value: Ty
    closed: bool = False


@dataclass(frozen=True)
class Snapshot:
    owner: int
    revision: int
    scope: int
    mode: str
    allocated: frozenset[int] = frozenset()
    bindings: tuple[tuple[int, Binding], ...] = ()

    @property
    def stamp(self) -> tuple[int, int, int, str]:
        return self.owner, self.revision, self.scope, self.mode


def normalize(t: Ty, s: Snapshot, visiting: frozenset[int] = frozenset()) -> Ty:
    """Read-only, including transitive reads through closed bindings."""
    if t.op == "var":
        key = t.label
        if not isinstance(key, int) or key not in s.allocated:
            raise Blocked("candidate is not owned by this snapshot")
        if key in visiting:
            raise Blocked("recursive candidate graphs are outside this experiment")
        binding = dict(s.bindings).get(key)
        if binding is None:
            raise Blocked("an unbound candidate is not an inferred bottom type")
        return normalize(binding.value, s, visiting | {key})
    if t.op == "atom":
        return t
    args = tuple(normalize(a, s, visiting) for a in t.args)
    if t.op == "union":
        return join(*args)
    if t.op in ("tuple", "record", "field"):
        return Ty(t.op, args, t.label)
    if t.op == "element" and len(args) == 1 and args[0].op == "tuple":
        return join(*args[0].args)
    if t.op == "arity" and len(args) == 1 and args[0].op == "tuple":
        return atom(f"arity:{len(args[0].args)}")
    if t.op == "keys" and len(args) == 1 and args[0].op == "record":
        return join(*(atom(f"key:{f.label}") for f in args[0].args))
    raise Blocked(f"unsupported normalization: {t.op}")


def included(a: Ty, b: Ty) -> bool:
    """Only immutable structures; this is NOT mutable-array/record subtyping."""
    if a == b:
        return True
    if a.op == "union":
        return all(included(x, b) for x in a.args)
    if b.op == "union":
        return any(included(a, x) for x in b.args)
    if a.op == b.op == "tuple":
        return len(a.args) == len(b.args) and all(
            included(x, y) for x, y in zip(a.args, b.args)
        )
    if a.op == b.op == "record":
        fields = {f.label: f.args[0] for f in a.args}
        return all(f.label in fields and included(fields[f.label], f.args[0]) for f in b.args)
    return False


@dataclass(frozen=True)
class Query:
    op: str
    source: Ty
    target: Ty

    def holds(self, s: Snapshot) -> bool:
        a, b = normalize(self.source, s), normalize(self.target, s)
        if self.op == "sub":
            return included(a, b)
        if self.op == "equal":
            return a == b
        raise Blocked(f"unsupported judgment: {self.op}")


@dataclass(frozen=True)
class Receipt:
    owner: int
    obligation: int
    stamp: tuple[int, int, int, str]
    _issued: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class Proposal:
    parent: int
    scope: int
    query: Query
    preview: bool  # Diagnostic information, NEVER acceptance evidence.


@dataclass(frozen=True)
class Observation:
    value: Ty
    receipt: Receipt


@dataclass(frozen=True)
class Accepted:
    stamp: tuple[int, int, int, str]
    obligations: tuple[int, ...]
    _issued: object = field(repr=False, compare=False)


@dataclass(frozen=True)
class Saved:
    snapshot: Snapshot
    legacy_version: int
    obligations: tuple[tuple[int, Query], ...]


class Owner:
    """An inference owner plus the only gate for acceptance-relevant results."""

    def __init__(self, scope: int | None = None) -> None:
        self._snapshot = Snapshot(next(_ids), next(_ids), scope or next(_ids), "normal")
        self._obligations: dict[int, Query] = {}
        self._checks: dict[int, Receipt] = {}
        self.legacy_version = 0  # Illustrates why the old rewound counter is not a stamp.
        self.evaluations = 0
        self._retired = False

    @property
    def snapshot(self) -> Snapshot:
        return self._snapshot

    def _ensure_open(self) -> None:
        if self._retired:
            raise Misuse("published owner is immutable; start a new owner")

    def _change(self, **fields: object) -> None:
        self._ensure_open()
        self._snapshot = replace(self._snapshot, revision=next(_ids), **fields)
        self._checks.clear()  # Coarse invalidation first; no dependency graph yet.

    def _key(self, v: Ty) -> int:
        if v.op != "var" or not isinstance(v.label, int) or v.label not in self.snapshot.allocated:
            raise Misuse("not a candidate allocated in this owner")
        return v.label

    def _scoped(self, t: Ty) -> None:
        if t.op == "var":
            self._key(t)
        for a in t.args:
            self._scoped(a)

    def fresh(self) -> Ty:
        key = next(_ids)
        self._change(allocated=self.snapshot.allocated | {key})
        self.legacy_version += 1
        return Ty("var", label=key)

    def bind(self, v: Ty, value: Ty, *, closed: bool = False) -> None:
        key = self._key(v)
        self._scoped(value)
        bindings = dict(self.snapshot.bindings)
        if key in bindings:
            raise Misuse("bind only determines an unbound candidate")
        bindings[key] = Binding(value, closed)
        self._change(bindings=tuple(sorted(bindings.items())))
        self.legacy_version += 1

    def grow(self, v: Ty, value: Ty) -> bool:
        """A proposal operation: even returning normally is not validation."""
        self._ensure_open()
        key = self._key(v)
        self._scoped(value)
        bindings = dict(self.snapshot.bindings)
        previous = bindings.get(key)
        if previous and (previous.closed or self.snapshot.mode == "frozen"):
            return False
        result = join(previous.value, value) if previous else value
        if previous and result == previous.value:
            return False
        bindings[key] = Binding(result)
        self._change(bindings=tuple(sorted(bindings.items())))
        self.legacy_version += 1
        return True

    def seal(self, v: Ty) -> bool:
        self._ensure_open()
        key = self._key(v)
        bindings = dict(self.snapshot.bindings)
        previous = bindings.get(key)
        if previous is None:
            raise Blocked("the model does not choose top by reading a hole")
        if previous.closed or self.snapshot.mode == "frozen":
            return False
        bindings[key] = replace(previous, closed=True)
        self._change(bindings=tuple(sorted(bindings.items())))
        self.legacy_version += 1
        return True

    def set_mode(self, mode: str) -> None:
        self._ensure_open()
        if mode not in ("normal", "frozen"):
            raise ValueError(mode)
        if mode != self.snapshot.mode:
            self._change(mode=mode)

    def save(self) -> Saved:
        return Saved(self.snapshot, self.legacy_version, tuple(self._obligations.items()))

    def restore(self, saved: Saved) -> None:
        self._ensure_open()
        if saved.snapshot.owner != self.snapshot.owner:
            raise Misuse("cannot restore another owner's transaction")
        self._snapshot = replace(saved.snapshot, revision=next(_ids))
        self._obligations = dict(saved.obligations)
        self._checks.clear()
        self.legacy_version = saved.legacy_version

    def _fork(self) -> Owner:
        child = Owner(self.snapshot.scope)
        child._snapshot = replace(self.snapshot, owner=child.snapshot.owner, revision=next(_ids))
        child.legacy_version = self.legacy_version
        # Parent obligations are not speculative-child obligations. No receipt transfer.
        return child

    def probe(self, query: Query, infer: Callable[[Owner], None] = lambda _: None) -> Proposal:
        child = self._fork()
        infer(child)
        return Proposal(self.snapshot.owner, self.snapshot.scope, query, query.holds(child.snapshot))

    def replay(self, proposal: Proposal) -> Receipt:
        if not isinstance(proposal, Proposal) or (
            proposal.parent != self.snapshot.owner or proposal.scope != self.snapshot.scope
        ):
            raise Misuse("proposal belongs to another parent or binder scope")
        # Ignore preview. Recheck ORIGINAL operands in the live owner's immutable snapshot.
        return self.require(proposal.query)

    def _check(self, identity: int) -> Receipt:
        cached = self._checks.get(identity)
        if cached is not None and cached.stamp == self.snapshot.stamp:
            return cached
        self.evaluations += 1
        if not self._obligations[identity].holds(self.snapshot):
            raise Invalid(f"obligation {identity} no longer holds")
        receipt = Receipt(self.snapshot.owner, identity, self.snapshot.stamp, _issuer)
        self._checks[identity] = receipt
        return receipt

    def require(self, query: Query) -> Receipt:
        self._ensure_open()
        identity = next(_ids)
        self._obligations[identity] = query  # Failure remains pending until rollback/revalidation.
        return self._check(identity)

    def use(self, receipt: Receipt, expected: Query | None = None) -> Receipt:
        if not isinstance(receipt, Receipt) or receipt._issued is not _issuer:
            raise Misuse("a proposal or arbitrary value is not evidence")
        if receipt.owner != self.snapshot.owner or receipt.obligation not in self._obligations:
            raise Misuse("foreign or rolled-back evidence")
        if expected is not None and self._obligations[receipt.obligation] != expected:
            raise Misuse("evidence proves a different judgment")
        return self._check(receipt.obligation)

    def observe(self, source: Ty) -> Observation:
        value = normalize(source, self.snapshot)
        # Retain the lost dependency even if downstream code uses only the frozen value.
        return Observation(value, self.require(Query("equal", source, value)))

    def consume(self, result: Observation) -> Ty:
        self.use(result.receipt)
        query = self._obligations[result.receipt.obligation]
        if query.op != "equal" or query.target != result.value:
            raise Misuse("materialized result does not match its provenance")
        return result.value

    def finish(self) -> Accepted:
        for identity in self._obligations:
            self._check(identity)
        return Accepted(self.snapshot.stamp, tuple(self._obligations), _issuer)

    def publish(self, accepted: Accepted) -> None:
        if not isinstance(accepted, Accepted) or accepted._issued is not _issuer:
            raise Misuse("not an acceptance certificate")
        if accepted.stamp != self.snapshot.stamp or accepted.obligations != tuple(self._obligations):
            raise Misuse("acceptance does not cover this state and every active obligation")

    def close(self) -> Accepted:
        """Final publication retires the owner; no later inference may change it."""
        accepted = self.finish()
        self.publish(accepted)
        self._retired = True
        return accepted
