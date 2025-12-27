## Self-contained repros: modeling collections in SKJS

This folder contains **small, self-contained TypeScript programs** meant to illustrate why
modeling Skip runtime collections is hard in SKJS:

- SKJS intentionally supports a **sound subset** of TypeScript.
- Some TypeScript features that are commonly used in library typing are **not supported** in SKJS.
- Some TypeScript assignability rules are **unsound** (by design) but widely relied upon; SKJS rejects them.

Each file is a single repro. Most include:
- **mini library subset**: a few `type`/`interface` declarations approximating the runtime API.
- **mini user code**: the smallest class/function that triggers the issue.

### How to run

From repo root:

- **TypeScript**: `npx -y -p typescript@5.7.3 tsc --noEmit -p tests/repros/top-signatures/tsconfig.json`
- **SKJS** (inside the Skip Docker image, per repo convention): run the generated examples checker or invoke `skjs check` directly.

### Repros

- **`repro-1-postfix-nonnull.ts`**: `expr!` is accepted by `tsc`, rejected by SKJS.
- **`repro-2-invalid-implements-variance.ts`**: classic variance/unsoundness mismatch (`implements` passes in TS, fails in SKJS).
- **`repro-3-namedcollections-constraint.ts`**: shows why constraining `Inputs` to a string-index signature forces unwanted widening/subtyping.
- **`repro-4-json-constraint.ts`**: illustrates the pain of a recursive `Json` encoding + `V extends Json` constraints.
- **`repro-5-extends-json-generic-constraint.ts`**: minimal repro that SKJS does not support generic constraints of the form `T extends Json` (TypeScript accepts them).

### Design sketches (not repros)

- **`design-inputcollections-initialdata.ts`**: design sketch proposing a sound API for named input collections + initial data.

#### Key technique: modeling existential types

The core challenge is handling *heterogeneous* collections — each `EagerCollection<K,V>` has its own K and V. We can't store them in `{ [name: string]: EagerCollection<Json,Json> }` (unsound due to variance), but TypeScript can't directly express "∃K,V. EagerCollection<K,V>" (there exist some K and V).

The design sketch uses **branded abstract base classes** to model existential types:

- `AbstractEagerCollection` represents `∃K,V. EagerCollection<K,V>` — "some collection with forgotten K,V"
- Concrete `EagerCollection<K,V>` extends the base, "packaging" the type witness
- The brand (protected field) makes the type nominal, so only real collections match

This is a standard OOP encoding of existentials, seen in Scala (abstract type members), Haskell (explicit `forall`), and Java/TypeScript (abstract base classes).

