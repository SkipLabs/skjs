# Intersection types against the model

A design note, ahead of any Lean. TypeScript uses intersection types in a
handful of recurring patterns. This asks, for each, whether the semantic model
in [SEMANTICS.md](SEMANTICS.md) can state the conjuncts, whether their
conjunction is inhabited, and what extension of the model the pattern needs
when it needs one. The point is to decide what to build before proving
anything about it.

## What the model fixes

Three definitions carry the whole analysis.

```lean
Fam := (n : Nat) → WorldT n → Val → Prop
interT A B := fun n W v => A n W v ∧ B n W v
refT T   := fun k W v => ∃ l c, v = .loc l ∧ lookup W l = some c ∧
              ∀ j < k, ∀ W' u, c j W' u ↔ T j W' u
arrowT A B := fun k W v => (∃ b, v = .lam b ∧ Scoped 1 b) ∧
              ∀ j < k, ∀ W' ⊒ W, ∀ h, HeapOk j W' h → ∀ a, A j W' a → Safe B j W' h (callBody v a)
```

So:

- **Intersection is always definable.** It is pointwise conjunction of two
  families, and it preserves admissibility. No pattern below fails because the
  connective is missing; a pattern fails because a conjunct cannot be stated,
  or because the conjunction is empty.
- **Values have five shapes**: `nul`, `undef`, `tru`, `fls`, a location, a
  closure. Two families that admit only different shapes have an empty
  conjunction. That single fact sorts the patterns into three kinds: a
  conjunction of contracts on one closure, a conjunction of contracts on one
  location, and a conjunction across shapes, which is empty until the
  representation of values changes.
- **A reference is invariant.** `refT T` says the location's stored contract
  *equals* `T` at every lower level. Two reference contracts on one location
  are therefore either the same contract or contradictory. This is the fact
  behind E3, and it is also what blocks width subtyping on references until
  contracts become field-wise.
- **An arrow is a contract on behaviour**, quantified over every future world
  and heap. Two arrow contracts on one closure are compatible whenever one
  body meets both, which the `lam` rule establishes by proving the body once
  per contract.

## The patterns

### 1. Overload sets: `((x: string) => number) & ((x: number) => string)`

**In the model now.** A closure in `arrowT A B ∧ arrowT C D` is one body that
is safe at `B` on `A` and at `D` on `C`. Introduction is the `lam` rule, one
derivation per conjunct; elimination is `app`, which picks a conjunct. This is
the refinement-types reading (Forsythe, Davies–Pfenning), and it is strictly
more precise than TypeScript's, which checks a single annotated signature
against each conjunct and never types a body twice. The identity at
`(boolean → boolean) & (null → null)` is the separating example: inhabited
here, rejected by `tsc`.

Resolution order is not a semantic matter. Any conjunct whose domain admits the
argument is a sound choice; first-match is TypeScript's convention and the
adapter follows it.

Two laws one might expect, of which only the second holds:

```
(A → B) ∧ (A → C)  =  A → (B ∧ C)    refuted
(A → C) ∧ (B → C)  =  (A ∨ B) → C    arrowT_union_dom
```

The first fails left to right: `ModelBoundaries.arrow_inter_codomain_fails`
exhibits a function in both `null → Ref(null)` and `null → Ref(null | boolean)`
that is in neither result's conjunction, because each call allocates and the
two contracts are invariant. `Safe` at a conjunction of result families is not
safety at each when the result is allocated. What does hold is the overload law,
`TypeAlgebra.overload_append`: an intersection of arrows is exactly the arrow
family over the concatenated signature list, with no distribution into the
result.

### 2. Disjoint-field composition: `{ name: string } & { createdAt: number }`

**Implemented.** The pattern is one object under two contracts that speak about
different fields, and it is the most common intersection in TypeScript (mixins,
`PropsWithChildren`, `Omit<T, k> & { k: New }`). Under the old one-location
reading it was empty: `refT P ∧ refT Q` needed the stored contract to equal both
`P` and `Q`. The fix was not to weaken invariance but to move it to the field.

**An object is a finite map from field names to locations, fixed at
allocation.** `Tm.objAt fields call` carries that map; `makeAt code names inits`
takes one fresh location per named field; `readAt f` and `writeAt f` go to the
location the map gives `f`. A location still holds one value under one contract,
so worlds, `HeapOk`, `read_sound` and `write_sound` are unchanged, and allocating
a whole object is the old single allocation iterated (`heap_allocs`,
`make_fields_rule`). That is the one place this differs from the sketch that
stood here: the field map lives in the value rather than in the world, which
leaves the heap model alone.

- `recT fs`, for `fs` a list of `(field, Fam)`, holds of an object whose map
  has, at each named field, a location under exactly that contract. Fields the
  type does not name are unconstrained: the type is open, as TypeScript's
  structural types are.
- `refT A` is `recT [(value, A)]`, and the `refs` clause carries a conjunction
  of field maps rather than of whole-cell contracts. `CoversFields` and
  `covers_recs` compare them field by field, so two operands naming disjoint
  fields constrain different locations and the conjunction is the composed
  record rather than the empty type.
- Width subtyping is sound for the same reason: every named field keeps its
  exact contract, and an unnamed one is not constrained.

### 3. Overlapping keys: `{ value: null } & { value: boolean }`

**Same field, two contracts.** Three cases, and the model already separates
them where TypeScript merges them.

- *Mutable field, different contracts.* Empty. A location cannot hold `null`
  invariantly and `boolean` invariantly. This is the sound verdict, and it is
  where TypeScript's covariant merge to `{ value: null & boolean }` and SKJS's
  merge both go wrong. SKJS's `TField::inter` meets the read types and joins
  the write types of a shared field, giving a field readable at `never` and
  writable at `null | boolean`, with no check that the two invariants agree;
  that is what admits both writes and the read back at `null`. `tsc` recovers
  by reducing the merged property to `never`; the model never merges.
- *Mutable field, same contract.* The plain cell. `{ value: boolean } &
  { value: true | false }` is `{ value: boolean }`, which the lowering already
  produces by deduplicating operands.
- *Read-only field.* Covariant merge is sound. A read-only view is a location
  whose stored contract at the field is *included* in the type rather than
  equal to it: `readT A` says the stored contract `I` satisfies `I ≤ A`. Then
  `readT A ∧ readT B = readT (A ∧ B)`, exactly TypeScript's merge, and it is
  right because no write can go through the view. Write-only views are the
  contravariant mirror. The claim boundary already carries this split, as the
  read and write types of a cell contract in `CellUnion`; giving it a
  semantics needs the stored contract to be quantified over, which the world
  makes available.

`Object.assign(a, b)` is typed `A & B` and is the everyday producer of
overlapping keys. The value it builds has `b`'s contract on every shared field,
so its sound type is the right-biased merge of two records, an operation on
field maps, not an intersection. When keys overlap with different contracts the
intersection type is simply false of the result.

### 4. Callable with properties: `(() => void) & { cancel(): void }`

**Empty across shapes.** A closure is not a location, so no value is in
`arrowT` and in `recT` at once. JavaScript functions are objects, and the
pattern is real (`debounce`, `memoize`, decorated handlers). The designs that
add the missing shape, and their rules, are compared in
[Callables](PROGRAM-TYPING.md#callables); what follows is the boxing design,
which that comparison recommends against.

The extension is to represent a function as a location whose field map has a
distinguished callable slot holding the closure, alongside ordinary fields.
Application reads the slot and applies. Then the pattern is a record with a
`call` field and a `cancel` field, inhabited and composed by rule 2.

Costs and a benefit. Every application goes through the heap, and closures
acquire an allocation site. The benefit is identity: a boxed function is a
location, so function identity is location identity, which the design notes
list as the missing piece for reproducing SKJS's equality branch on arrows
(`L-INTER-BOT`, [DESIGN.md](DESIGN.md#valuable-later-targets-and-the-traps-they-introduce)).
Extensional arrow membership cannot give that; boxing does.

### 5. Branding: `string & { readonly __brand: "UserId" }`

**Empty by shape, and meant to be.** A primitive is not a location. No runtime
value has the brand, and TypeScript's idiom relies on that: the intersection is
a phantom tag, entered only by an assertion in a constructor. The model agrees
that the type is uninhabited and locates the unsoundness in the cast. What the
idiom wants is a generative abstract type, a nominal refinement of `string`,
which is a different feature from intersection and outside the current type
language. Not an intersection pattern; do not model it as one.

### 6. Narrowing results: `x instanceof Bar`, `"k" in x`

Two different extensions.

- `"k" in x` on `x : recT fs` narrows to `recT (fs ++ [(k, ⊤)])`. With
  multi-field references this is a tag test on locations, in the family of
  `isNul`, `isBool`, `isUndef`: a `hasField k` tag, answered by the stored
  field map. Sound and cheap once rule 2 exists.
- `instanceof` needs nominal tags on locations: a class identity carried in the
  stored contract, fixed at allocation. `Foo & Bar` is then inhabited when a
  location can carry both tags, which is the subclass relation. This is a
  separate extension, tagged locations, and it is what the `ACCESSOR-METHOD`
  and callability targets in the design notes would also need.

### 7. Generic bounds and markers: `T extends A & B`, `ThisType<T>`

A bound is membership in the intersection; nothing new semantically, but
polymorphism is outside the model's current scope
([SEMANTICS.md](SEMANTICS.md#remaining-scope)). `ThisType` and similar markers
carry no runtime meaning and have no semantic content to model.

## Summary

| Pattern | Now | Verdict | Extension |
| --- | --- | --- | --- |
| Overload sets | in the model | inhabited iff one body meets each; more precise than TS | none |
| Disjoint-field composition | inhabited, equals the composed record | as the model now has it | done |
| Overlapping mutable keys | empty | empty; the sound verdict | none |
| Overlapping read-only keys | not statable | covariant merge, sound | read/write field capabilities |
| Callable with properties | empty | inhabited once functions are locations | boxed functions |
| Branding | empty | empty, as intended; the cast is the unsound step | none; a nominal type if ever |
| `in` narrowing | not statable | tag on locations | a `hasField` tag, answered by the object's own map |
| `instanceof` narrowing | not statable | subclass relation on tags | tagged locations |
| Generic bounds | out of scope | membership in the intersection | polymorphism |

## Order of extensions

1. ~~**Multi-field references with per-field invariance.**~~ Done. An object is
   a map from field names to locations; the clause language, the typing and
   certificate rules, the source lowering and both producers name the field
   they are about, and a current-content assertion does too.
2. **Read and write capabilities on a field.** Gives the claim boundary's
   read/write split a semantics and makes TypeScript's covariant merge sound
   exactly where it is sound. Small once fields are individual.
3. **Callable values.** Unlocks callable-with-properties and function identity.
   Either a lowering over multi-field references or a value shape of its own;
   [Callables](PROGRAM-TYPING.md#callables) compares them with boxing, which
   changes application and every closure, and does nothing for overloads.
4. **Tagged locations.** Unlocks `instanceof` and class-based narrowing.

## What it says about SKJS

SKJS's merge of `{ value: null } & { value: boolean }`, reads met to `never`
and writes joined to `null | boolean`, is the read-only law applied to a
mutable field, with the write side widened rather than required to agree. The sound rule the model gives
is: on disjoint fields, compose; on a shared read-only field, intersect the
contracts; on a shared mutable field, require the same contract and otherwise
report the type empty. TypeScript's `never` reduction is that last clause,
applied late. For arrows, the sound rule is that a conjunction of signatures is
a type in its own right, inhabited by any function meeting each; `never` is
never the answer for two arrows. SKJS gives that answer today: `TFun::inter`
(`src/TTypeInter.sk`) returns `None` unless one signature is a subtype of the
other, and that `None` propagates through `TFields::inter` and `TObject::inter`
until the clause is dropped, so `((x: string) => number) & ((x: number) =>
string)` is empty in the checker. The repair the model prescribes is the one
`overload_append` states: let `Callability::CPresent` carry a set of signatures
and concatenate on `inter`. Boxing functions does not help here and makes it
worse — see [Callables](PROGRAM-TYPING.md#callables), design A.
