// A minimal slice of the code skipper generates for a reactive service, in the
// form it emits after the json-index-sig change ("Emit a string index signature
// on generated object types"): every generated value/key object type is
// intersected with `{ readonly [key: string]: Json | null }` so it is a sound
// `Json` subtype.
//
// That change is necessary but NOT sufficient to make the generated service
// type-check under skjs. It fixes the VALUE side — the indexed `Value` satisfies
// the `K/V extends Json` bounds, so the generated `Mapper` below is accepted —
// but a generated collection-record type like `GraphCollections` is passed where
// `NamedCollections = { [name: string]: EagerCollection<Json, Json> }` is
// required, on `Resource` (and `SkipService`). `EagerCollection<K, V>` is
// contravariant in K (`getArray(key: K)`) and invariant in V, so a concretely-
// typed `EagerCollection<Id, Value>` is NOT a subtype of
// `EagerCollection<Json, Json>`: widening the key to `Json` would let a `boolean`
// key reach `getArray`, which expects `string` — hence the witness "Type boolean
// is not assignable to type string". skjs rejects this soundly; TypeScript
// accepts it only through method-parameter bivariance.
//
// So adding index signatures cannot fix the generated service end-to-end — the
// remaining gap is in the `@skipruntime/core` API type design, which pins
// collection K/V to `Json`. (See index-signatures.ts Test 25 for the underlying
// rejection that the index signature is meant to address: a named-field object
// type is not a sound subtype of an index signature it does not itself declare.)
//
// The generated `class Service implements SkipService<Inputs, ResourceInputs>` is
// rejected the same way on its `… extends NamedCollections` bounds; it is omitted
// here because that failure surfaces inside the library stub (via
// `initialData?: InitialData<Inputs>`), where it cannot carry an annotation.

import type {
  Context,
  EagerCollection,
  Json,
  Mapper,
  Resource,
  Values,
} from "@skipruntime/core";

// Generated key/value types, in the post-json-index-sig form.
type Id = string;
type Value = { readonly n: number } & { readonly [key: string]: Json | null };

// A generated collection-record type: named, with concretely-typed collections.
type GraphCollections = { input: EagerCollection<Id, Value> };

// Accepted: the indexed `Value` satisfies the `K1/V1/K2/V2 extends Json` bounds,
// so the value side the skipper change targets type-checks.
export class IdentityMapper implements Mapper<Id, Value, Id, Value> {
  mapEntry(
    key: Id,
    values: Values<Value>,
    _context: Context,
  ): Iterable<[Id, Value]> {
    return [[key, values.getUnique()]];
  }
}

// Rejected two ways, both from EagerCollection's variance:
//  - the `instantiate` return `EagerCollection<Id, Value>` is not assignable to
//    the interface's `EagerCollection<Json, Json>` → "incorrectly implements";
//  - the type argument `GraphCollections` does not satisfy the constraint
//    `Collections extends NamedCollections`.
// @skjs-expect-error This class incorrectly implements 'Resource'
// @skjs-expect-error Type argument does not satisfy the constraint
export class GraphResource implements Resource<GraphCollections> {
  instantiate(
    cs: GraphCollections,
    _context: Context,
  ): EagerCollection<Id, Value> {
    return cs.input;
  }
}
