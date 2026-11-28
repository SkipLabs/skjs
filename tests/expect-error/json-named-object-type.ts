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

// Rejected through the `Json` union (the issue's verbatim repro).
interface JsonBox<T extends Json> {
  get(): T;
}
// @skjs-expect-error Type argument does not satisfy the constraint
// @skjs-expect-error-line2 This is of type: 'Named'
// @skjs-expect-error-line3 It does not satisfy the constraint: 'Json'
// @skjs-expect-error-line4 Type '{ readonly a: string; }'
// @skjs-expect-error-line5 is not assignable to type 'readonly (null | Json)[]'
// @skjs-expect-error-line6 The field 'every' is missing
// @skjs-expect-error-line7 Type '{ readonly a: string; }'
// @skjs-expect-error-line8 is not assignable to type '{ readonly [key: string]: null | Json; }'
// @skjs-expect-error-line9 Missing index signature 'key' in source type
export class JsonC implements JsonBox<Named> {
  get(): Named {
    return { a: "x" };
  }
}

// Direct return of a named object type against `Json`.
function namedAsJson(x: Named): Json {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type '{ readonly a: string; }'
  // @skjs-expect-error-line3 is not assignable to type 'readonly (null | Json)[]'
  // @skjs-expect-error-line4 The field 'every' is missing
  // @skjs-expect-error-line5 Type '{ readonly a: string; }'
  // @skjs-expect-error-line6 is not assignable to type '{ readonly [key: string]: null | Json; }'
  // @skjs-expect-error-line7 Missing index signature 'key' in source type
  return x;
}

// Named object type against an explicit index-signature | array union.
function namedAsIndexOrArray(
  x: Named,
): { readonly [k: string]: string } | readonly string[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type '{ readonly a: string; }'
  // @skjs-expect-error-line3 is not assignable to type 'readonly string[]'
  // @skjs-expect-error-line4 The field 'every' is missing
  // @skjs-expect-error-line5 Type '{ readonly a: string; }'
  // @skjs-expect-error-line6 is not assignable to type '{ readonly [k: string]: string; }'
  // @skjs-expect-error-line7 Missing index signature 'k' in source type
  return x;
}

// Symmetric: an array failing against an index-signature | array union should
// blame the array branch rather than the index-signature branch.
function arrayAsIndexOrArray(
  x: readonly string[],
): { readonly [k: string]: number } | readonly number[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type 'string'
  // @skjs-expect-error-line3 is not assignable to type 'number'
  // @skjs-expect-error-line4 Function parameter types are checked contravariantly: target parameter type 'string' must be assignable to source parameter type 'number'
  // @skjs-expect-error-line5 Type '(this: readonly string[], (string) => boolean) => boolean'
  // @skjs-expect-error-line6 is not assignable to type 'number'
  return x;
}

// Fallback: when NO target branch matches the source's array-ness (e.g. a
// non-array object against a union of array types), keep all failing branches.
function namedAsArrayUnion(x: Named): readonly string[] | number[] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line2 Type '{ readonly a: string; }'
  // @skjs-expect-error-line3 is not assignable to type 'readonly string[]'
  // @skjs-expect-error-line4 The field 'every' is missing
  // @skjs-expect-error-line5 Type '{ readonly a: string; }'
  // @skjs-expect-error-line6 is not assignable to type 'number[]'
  // @skjs-expect-error-line7 The field 'concat' is missing
  return x;
}

// Rejected through `JsonObject` (no array-branch noise), so the actionable
// reason — that the source supplies no index signature — is surfaced cleanly
// at default error detail, naming the source type and the missing index.
interface ObjBox<T extends JsonObject> {
  get(): T;
}
// @skjs-expect-error Type argument does not satisfy the constraint
// @skjs-expect-error-line2 This is of type: 'Named'
// @skjs-expect-error-line3 It does not satisfy the constraint: 'JsonObject'
// @skjs-expect-error-line4 Type '{ readonly a: string; }'
// @skjs-expect-error-line5 is not assignable to type '{ readonly [key: string]: null | Json; }'
// @skjs-expect-error-line6 Missing index signature 'key' in source type
export class ObjC implements ObjBox<Named> {
  get(): Named {
    return { a: "x" };
  }
}

// A sound workaround: intersecting an explicit index signature in makes the
// named type a `Json` subtype, because every field is itself JSON-shaped
// (recursively). Accepted under the same constraint that rejects the bare
// type above. This is skipper's original approach (skipper#1217) — it works,
// but the wider inferred shape breaks unrelated real-`tsc` inference like
// `deepFreeze<T>` (skipper#1239), which `Closed<T>` below does not.
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

// The preferred sound workaround, and the shape a value/key-type generator
// now emits (skipper's generator switched to this — see skipper#1239): wrap
// the named type in `Closed<T>` instead of intersecting an index signature.
// `Closed<T>` is the identity under `tsc` (no widening, no `deepFreeze<T>`
// breakage) and a sound `Json` subtype under skjs.
type ClosedNamed = Closed<{ readonly a: string }>;
function closedIsJson(x: ClosedNamed): Json {
  return x;
}
type ClosedRealistic = Closed<{
  readonly title: string;
  readonly email?: string;
  readonly dueDate?: number | null;
  readonly meta: Closed<{ readonly tag: string }>;
}>;
function closedRealisticIsJson(x: ClosedRealistic): Json {
  return x;
}
