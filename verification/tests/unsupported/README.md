# Unsupported source examples

These are readable boundary cases, not verified successes. `unsupported.mts`
runs `instanceof_narrow.ts` and `mutable_binding.ts` through the pipeline and
requires each refusal for its specific limitation, so an unrelated failure
cannot silently replace the intended gate; `in_inherited.ts`'s refusal is the
pipeline case `in-inherited-refused`'s.

- `in_inherited.ts`: `"toString" in x`, a key every object inherits from
  `Object.prototype`, which the model's own-key test does not see.
- `instanceof_narrow.ts`: `x instanceof C` for a constructor `C` passed in,
  whose instances' prototype nothing in the file names.
- `mutable_binding.ts`: a `let` with neither an initializer nor an annotation.

The viewer labels this group **Unsupported examples · expected limitations**.
See [the regression guide](../README.md) for promotion criteria.
