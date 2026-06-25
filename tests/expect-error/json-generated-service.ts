// A minimal slice of the code skipper generates for a reactive service, in the
// form it emits after the json-index-sig change ("Emit a string index signature
// on generated object types"): every generated value/key object type is
// intersected with `{ readonly [key: string]: Json | null }` so it is a sound
// `Json` subtype.
//
// That change is necessary but NOT sufficient on its own. It fixes the VALUE
// side — the indexed `Value` satisfies the `K/V extends Json` bounds, so the
// generated `Mapper` below is accepted. The generated `Resource<GraphCollections>`
// would be REJECTED by a `NamedCollections`-style API, where `Resource<C>` is
// parameterized by `C extends { [name: string]: EagerCollection<Json, Json> }`:
// `EagerCollection<K, V>` is contravariant in K (`getArray(key: K)`), so a
// concretely-typed `EagerCollection<Id, Value>` is not a subtype of
// `EagerCollection<Json, Json>`. TypeScript accepts it through method-parameter
// bivariance; skjs rejects it soundly.
//
// With the existential API — `Resource<C extends SharedCollections>` where
// `SharedCollections = { readonly [name: string]: AbstractEagerCollection |
// AbstractLazyCollection }` and `EagerCollection<K, V> extends
// AbstractEagerCollection` — the `interface GraphCollections extends
// SharedCollections` form satisfies the bound: each named field is a
// concrete `EagerCollection<K,V>` which extends the abstract base class, and
// the `extends` clause satisfies the index-signature requirement via the
// alias-extends fix (skjs now accepts `interface X extends <type alias>`).
// `Resource<GraphCollections>` is ACCEPTED.

import type {
  Context,
  EagerCollection,
  Json,
  Mapper,
  Resource,
  SharedCollections,
  Values,
} from "@skipruntime/core";

// Generated key/value types, in the post-json-index-sig form.
type Id = string;
type Value = { readonly n: number } & { readonly [key: string]: Json | null };

// A generated collection-record interface extending SharedCollections:
// each named field is an EagerCollection, satisfying the index sig constraint
// through the AbstractEagerCollection base class + extends-alias inheritance.
interface GraphCollections extends SharedCollections {
  readonly input: EagerCollection<Id, Value>;
}

// Accepted: the indexed `Value` satisfies the `K1/V1/K2/V2 extends Json` bounds,
// so the value side the skipper change targets type-checks.
export class IdentityMapper implements Mapper<Id, Value, Id, Value> {
  mapEntry(
    key: Id,
    values: Values<Value>,
    _context: Context,
  ): Iterable<[Id, Value]> {
    const arr = values.toArray();
    const v = arr[0];
    if (v === undefined) return [];
    return [[key, v]];
  }
}

// Accepted with the existential API: `GraphCollections extends SharedCollections`,
// so `Resource<GraphCollections>` satisfies the `Collections extends
// SharedCollections` constraint without any variance check.
export class GraphResource implements Resource<GraphCollections> {
  instantiate(
    cs: GraphCollections,
    _context: Context,
  ): EagerCollection<Id, Value> {
    return cs.input;
  }
}
