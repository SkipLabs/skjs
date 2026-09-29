# Unsupported source examples

These are readable boundary cases, not verified successes. `unsupported.mts`
runs each through the pipeline and requires its refusal for a specific
limitation, so an unrelated failure cannot silently replace the intended gate.

- `in_inherited.ts`: `"toString" in x`, a key every object inherits from
  `Object.prototype`, which the model's own-key test does not see.
- `instanceof_narrow.ts`: `x instanceof C` for a constructor `C` passed in,
  whose instances' prototype nothing in the file names.
- `mutable_binding.ts`: mutable local bindings.

The viewer labels this group **Unsupported examples · expected limitations**.
See [the regression guide](../README.md) for promotion criteria.
