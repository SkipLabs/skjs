# OCaml producer prototype

An independent OCaml producer with **verified acceptance**, using the existing
Fragment → SourceClaims → Lean evidence pipeline. It does not invoke SKJS or
TypeScript's type checker to infer claims. The shared TypeScript parser remains
the source front end. The Lean model, lowering and proof rules are unchanged.

## Try it

From the repository root, with OCaml 5 installed:

```sh
npm ci --prefix verification/tools
lake -d verification/lean build verifier
make -C verification/ocaml-producer
node verification/ocaml-producer/check.mts verification/ocaml-producer/examples/callbacks.ts
make -C verification/ocaml-producer test
```

Set `VERIFIER` to reuse a verifier executable built from this checkout's Lean
sources. This avoids rebuilding Lean in a fresh worktree. The prototype requires
no OCaml packages beyond the standard library, and no Skip toolchain or Docker.

The checker prints `verified`, `unverified`, `unsupported`, or `error`, with an
artifact directory containing the exact source snapshot, Fragment, claims,
evidence (if produced), and diagnostic logs. Only `verified` exits successfully.
Proof search has fuel 12; each child process has a 30-second timeout. An
`unverified` result is not a proof that the source is wrong. A timeout or failed
executable is an infrastructure error. Artifacts remain available for inspection.

The low-level `_build/producer fragment.json` command **only proposes claims**.
Its successful exit is never a type-checking verdict.

## Architecture, including the parts not implemented yet

The scope limit is in the implemented cases, not a different account of the
language. The boundaries are:

1. `source.ml` decodes the shared Fragment into typed OCaml data. It preserves
   source positions, declared contracts, and quantified parameters with bounds.
   Unsupported constructs fail explicitly. It does not lower JavaScript into a
   second calculus; existing Lean lowering owns that step.
2. `semantic.ml` describes immutable semantic types. Rigid binder identity
   includes scope and binder index; spelling is only for export. Object shapes
   contain both field capabilities and call signatures. Fields distinguish
   presence, reads and writes; function objects will not require a second
   type universe. The initial decoder/exporter supports required invariant
   fields, while readonly/optional capabilities remain unimplemented.
3. `environment.ml` distinguishes immutable value snapshots from mutable
   storage contracts. In this implementation, mutable reads always propose
   the fixed storage type, including inside closures. No point-specific
   refinement or inference operation can replace that contract.
4. `proposal.ml` infers immutable candidate claims. It neither validates nor
   publishes acceptance. It conservatively joins branches and infers local
   values, object shapes, callback results and calls from explicit signatures.
   Declared types are candidates to prove, not proof that their bodies satisfy
   them. There is no second, approximate subtype relation used for acceptance.
5. `claims.ml` serializes those candidates into the existing producer-neutral
   SourceClaims protocol. Graph interning is local to one document. Graph
   labels are an export detail, not type-variable identities.
6. `check.mts` freezes source bytes, runs the parser and OCaml producer, asks Lean
   to reconstruct obligations and produce evidence, then invokes the independent
   evidence consumer. Every source function must be covered. Acceptance is
   printed only after that final check succeeds.

Inference metavariables and existential witnesses are **not implemented**.
When introduced, they must have separate identities and capabilities from rigid
binders. They belong to proposal/search state; they cannot be substituted into
published semantic types without discharging retained obligations. Likewise,
delayed literals are inference work, not new semantic types.

The intended extension order is contextual inference and constraint proposals,
then more source forms and stronger flow analysis. Keep the same boundary:
inference proposes; the independently reconstructed obligations decide whether
acceptance can be published. For inferred storage, solve a lifetime contract
against initialization and **all** writes before publication. For heap flow
facts, add location identity, alias tracking and invalidation; do not overwrite
field capabilities or snapshot types. Cache validated decisions only with their
complete assumptions/dependencies, separately from inference caches.

This is not a promise that full-language support needs no new representations.
For example, recursive types, effect summaries and general quantifier proofs
still need implementation and mathematical work. The invariants above must
survive those extensions rather than being replaced by subset shortcuts.

## What works and what the tests establish

Positive examples cover local inference, fixed mutable contracts, branches and
numeric arithmetic, multi-field objects and alias writes, multi-argument `.call`,
callbacks passed and returned, captured mutable storage, and rigid generic
identity/bounds. Generic support is the existing bounded variable-copy fragment,
not generic instantiation or general polymorphic inference.

Negative examples exercise return contracts, local and aliased writes, callback
arguments, captures, and fabrication of a rigid generic result. Separate tests
alter a source fingerprint, remove a function, falsify a point claim, and corrupt
evidence; the independent consumer must refuse them. These are checks of the
acceptance boundary, not just snapshots of the inferred types.

`generic-inferred.ts` deliberately remains **unverified**: the existing generic
source adapter requires an explicit type on a copied `const`. The annotated
version verifies. `unsupported.ts` demonstrates the producer's refusal to guess
an unannotated mutable binding's lifetime contract. Neither is counted as a
successful verification or silently rewritten into a simpler witness.

## What is proved, and what is trusted

Successful checking uses the existing Lean certificate consumer and its
soundness theorems for the modeled fragment. The OCaml inference algorithm is
not itself proved correct; a bad proposal must fail validation. Generic
variable-copy checking uses the existing direct generic checker in both Lean
phases rather than ordinary graph evidence.

The shared parser, source-to-calculus correspondence, executable toolchain and
runner remain part of the trust boundary. Source lowering being written in Lean
is not a proof of preservation of full JavaScript semantics. Existing model
assumptions and restrictions in [DESIGN.md](../DESIGN.md) still apply. This is a
first producer against that boundary, not a verified implementation of the full
TypeScript language.
