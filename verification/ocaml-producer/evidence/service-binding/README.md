# Evidence: Skip's service binding, unsound and sound

One crashing service, on two bindings, checked by the pipeline (parser →
OCaml → Lean). Each file declares the framework binding and uses it, so the
binding is part of what is checked.

The crashing service declares `input1` and reads `input2`. At run time the
runtime passes `createGraph` one collection per declared input, so the read
finds nothing.

- **Today's binding:**
  [`framework-binding-unsound.ts`](../../examples/framework-binding-unsound.ts).
  `createGraph`'s input type is a type parameter of its own, not tied to the
  declared inputs.
- **The sound binding:**
  [`crashing-service-sound-binding.ts`](crashing-service-sound-binding.ts)
  holds the crashing service, and
  [`framework-binding-sound.ts`](../../examples/framework-binding-sound.ts)
  the correct one. `createGraph` obtains each collection through the
  definition that declared it (`inputs.get(definition)`), at that
  definition's types.

## Results

`reproduce.sh` printed [`results.txt`](results.txt):

| Service | Binding | Pipeline |
| --- | --- | --- |
| crashing | today's | **verified** |
| crashing | sound | **refused** |
| correct | sound | **verified** |

- **Crashing service, today's binding: verified.** The binding describes the
  runtime wrongly, and relative to that description the service is well
  typed. The fault is the binding's, not the checker's.
- **Crashing service, sound binding: refused.** The read names an input the
  service does not declare ("Property 'input2' does not exist on type
  'OneDef'"). The refusal comes from the pipeline's front end, before Lean,
  because the program is ill-typed.
- **Correct service, sound binding: verified.**

"Verified" means Lean checked the certificate against the calculus, which is
proved safe. The theorems `verifyJson_safe`, `verifyJson_checked` and
`verify_closed_safe` depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), and the build contains no `sorry`. The
runtime enters only through its declared interface, so soundness assumes the
runtime keeps that interface's promise. The patched runtime keeps it; for a
definition the service did not declare, it throws a clear error.

## The change to Skip

[`skip-sound-service-binding.diff`](skip-sound-service-binding.diff) is the
same change against the pinned runtime (upstream `skip` commit `5c902f17`):

- `InputCollections.get`;
- `SkipService` without its free `Inputs` parameter;
- `runService` generic over the concrete service;
- `ResourceClass<R, Json>`, since the runtime calls resource constructors with
  the request's Json;
- the runtime handing out collections by definition;
- `reactive-sum-sound.ts` adapted.

It type-checks under `tsc` with no new errors against the pinned snapshot. The
real `sum.ts` on the patched runtime is not verified yet.
