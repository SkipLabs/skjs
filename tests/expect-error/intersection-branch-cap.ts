// An n-way intersection of two-branch object unions cross-products to 2^n
// branches; past the shared branch cap SKJS rejects the type as too complex
// rather than materializing it (previously this hung / exhausted memory with
// no diagnostic). tsc degrades gracefully at its own, higher limit (its
// TS2590 is ~100k constituents), so SKJS is stricter here. This test could not
// be pinned before the fix: the pre-fix behavior was an OOM, not an error.
// @skjs-expect-error This intersection produces too many object branches; the type is too complex to represent
type V0 = { v0: 0 } | { v0: 1 };
type V1 = { v1: 0 } | { v1: 1 };
type V2 = { v2: 0 } | { v2: 1 };
type V3 = { v3: 0 } | { v3: 1 };
type V4 = { v4: 0 } | { v4: 1 };
type V5 = { v5: 0 } | { v5: 1 };
type V6 = { v6: 0 } | { v6: 1 };
type V7 = { v7: 0 } | { v7: 1 };
type V8 = { v8: 0 } | { v8: 1 };
type V9 = { v9: 0 } | { v9: 1 };
type V10 = { v10: 0 } | { v10: 1 };
type V11 = { v11: 0 } | { v11: 1 };
type V12 = { v12: 0 } | { v12: 1 };
type V13 = { v13: 0 } | { v13: 1 };
type I = V0 &
  V1 &
  V2 &
  V3 &
  V4 &
  V5 &
  V6 &
  V7 &
  V8 &
  V9 &
  V10 &
  V11 &
  V12 &
  V13;
function usesTooComplexIntersection(x: I): number {
  return x.v0;
}
