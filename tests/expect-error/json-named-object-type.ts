// Issue #660: a named object TYPE used where `Json` / `JsonObject` is required.
//
// A named-field object type with no index signature of its own is NOT a sound
// subtype of `Json` / `JsonObject`. Object types are open under width
// subtyping, so the value may carry extra keys of unrelated types; treating it
// as indexed would let those be read at the index value type. TypeScript
// accepts this assignment and is unsound as a result, so skjs rejects it.
// Object-literal *values* are still accepted; to use a named type as `Json`,
// intersect it with an explicit `readonly [key: string]: Json | null` index.

import type { Json, JsonObject } from "@skipruntime/core";

type Named = { readonly a: string };

// Rejected through the `Json` union (the issue's verbatim repro). The union's
// array branch contributes noise, so only the top-level rejection is pinned.
interface JsonBox<T extends Json> {
  get(): T;
}
// @skjs-expect-error Type argument does not satisfy the constraint
export class JsonC implements JsonBox<Named> {
  get(): Named {
    return { a: "x" };
  }
}

// Rejected through `JsonObject` (no array-branch noise), so the actionable
// reason — that the source supplies no index signature — is surfaced cleanly
// at default error detail, naming the source type and the missing index.
interface ObjBox<T extends JsonObject> {
  get(): T;
}
// @skjs-expect-error Type argument does not satisfy the constraint
// @skjs-expect-error-line2 This is of type: Named
// @skjs-expect-error-line3 It does not satisfy the constraint: JsonObject
// @skjs-expect-error-line4 Type { readonly a: string }
// @skjs-expect-error-line5 is not assignable to type { readonly [ key: string ]: null | Json }
// @skjs-expect-error-line6 Missing index signature 'key' in source type
export class ObjC implements ObjBox<Named> {
  get(): Named {
    return { a: "x" };
  }
}

// The sound workaround — and the shape a value/key-type generator should emit:
// intersecting an explicit index signature in makes the named type a `Json`
// subtype, because every field is itself JSON-shaped (recursively). Accepted
// under the same constraint that rejects the bare type above.
type Indexed = { readonly a: string } & { readonly [key: string]: Json | null };
function indexedIsJson(x: Indexed): Json {
  return x;
}
type IndexedRealistic = {
  readonly title: string;
  readonly email?: string;
  readonly dueDate?: number | null;
  readonly meta: { readonly tag: string } & {
    readonly [key: string]: Json | null;
  };
} & { readonly [key: string]: Json | null };
function indexedRealisticIsJson(x: IndexedRealistic): Json {
  return x;
}
