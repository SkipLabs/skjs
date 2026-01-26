// Nullish coalescing on 'unknown' is valid because unknown may contain null/undefined

function withDefaultUnknown(x: unknown, def: unknown): unknown {
  return x ?? def;
}
