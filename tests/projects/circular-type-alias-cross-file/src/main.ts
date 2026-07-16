// A type alias that forwards, through another file, to a *different* alias of
// the same name is not circular: `Json` here resolves to `Bridge`, which
// resolves to other.ts's own `Json`, which is `string`. The chain ends there.
//
// The circularity check must therefore compare each resolved reference to the
// alias under test by definition rather than by name — the two `Json`s share a
// name and nothing else.
import { Bridge } from "./other";

export type Json = Bridge;

export function useJson(x: Json): string {
  return x;
}
