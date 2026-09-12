# Unsupported source examples

These are readable boundary cases, not verified successes. `unsupported.mts`
requires rejection for a specific limitation, so an unrelated failure cannot
silently replace the intended gate.

- `calls_and_consts.ts`: equality and general string/call support.
- `typeof_narrow.ts`: `typeof` tests and general primitive narrowing.
- `mutable_binding.ts`: mutable local bindings.
- `beyond_precision.ts`: a numeric-precision soundness target; the current
  verifier rejects unsupported equality, not the numeric narrowing itself.

The viewer labels this group **Unsupported examples · expected limitations**.
See [the regression guide](../README.md) for promotion criteria.
