# Unsupported source examples

These are readable boundary cases, not verified successes. `unsupported.mts`
requires rejection for a specific limitation, so an unrelated failure cannot
silently replace the intended gate.

- `in_inherited.ts`: `"toString" in x`, a key every object inherits from
  `Object.prototype`, which the model's own-key test does not see.
- `instanceof_narrow.ts`: `x instanceof C` for a constructor `C`, whose
  instances the model does not tell from other objects of their shape.
- `mutable_binding.ts`: mutable local bindings.

The string and call example that used to sit here is gone: strings are in the
fragment, and calls to declared functions are recorded as the ambient-value
boundary in [the coverage guide](../../REPAIR-COVERAGE.md). The
numeric-precision target that used to sit here now lives in
[`skjs-unsound/beyond-precision.ts`](../skjs-unsound/beyond-precision.ts):
with numbers and strings in the fragment it reaches proof search, where its
claims are not derived.

The viewer labels this group **Unsupported examples · expected limitations**.
See [the regression guide](../README.md) for promotion criteria.
