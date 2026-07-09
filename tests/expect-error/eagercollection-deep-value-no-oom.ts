// Regression guard for the recursive-generic OOM fixes (#736 mapTParams,
// #737 isSub TSInst fast path) that let the regenerated generated-examples
// (notably voting-system) type-check without blowing up. Chaining `.map` over
// an EagerCollection whose value type is a deeply-nested Json record exercises
// the recursive-generic subtype check (EagerCollection's methods reference
// EagerCollection itself). It must type-check in bounded time — ~0.5s here,
// vs ~2.3s before the fixes (and it OOMs at greater depth without them). No
// minimal case OOMs on current `main` (see #759), so this is a bounded-time
// perf guard rather than a hard hang test.
import type {
  EagerCollection,
  Json,
  Mapper,
  Values,
  Context,
} from "@skipruntime/core";
type Rec = {
  readonly id: string;
  readonly meta: { readonly n: number } & { readonly [k: string]: Json | null };
} & { readonly [key: string]: Json | null };
class M implements Mapper<string, Rec, string, Rec> {
  mapEntry(
    key: string,
    values: Values<Rec>,
    _c: Context,
  ): Iterable<[string, Rec]> {
    const v = values.toArray()[0];
    if (v === undefined) return [];
    return [[key, v]];
  }
}
export function build(
  c: EagerCollection<string, Rec>,
): EagerCollection<string, Rec> {
  return c.map(M);
}
