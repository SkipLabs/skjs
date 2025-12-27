// Repro: `T extends Json` (generic constraints) is not supported in SKJS today.
//
// This file is intentionally minimal: it only uses a generic constraint of the form
// `T extends Json` (no conditional types, no type predicates, no casts, no mapped types).
//
// Expected:
// - tsc: OK
// - skjs: error (generic constraints / `extends` are not supported)

// ===================== FRAMEWORK SUBSET =====================
// Keep Json/JsonObject exactly as in @skipruntime/core.
type Json = boolean | number | string | (Json | null)[] | JsonObject;
type JsonObject = { [key: string]: Json | null };

// ========================= USER CODE =========================
// Minimal use of `extends` as a *generic constraint*.
interface AcceptsJson<T extends Json> {
  value: T;
}

// ---- Should be accepted by TypeScript ----
const ok1: AcceptsJson<JsonObject> = { value: { name: "alice", extra: null } };
const ok2: AcceptsJson<Json> = { value: ok1.value };
const ok3: AcceptsJson<(Json | null)[]> = { value: [null, "x", 1, { k: "v" }] };

// ---- Should be rejected by TypeScript ----
// @ts-expect-error bigint is not part of Json
const bad1: AcceptsJson<bigint> = { value: 0n };

// @ts-expect-error functions are not Json
const bad2: AcceptsJson<() => void> = { value: () => {} };

// @ts-expect-error Date is not JsonObject (it has no string index signature)
const bad3: AcceptsJson<Date> = { value: new Date() };


