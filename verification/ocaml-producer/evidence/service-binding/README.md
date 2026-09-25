# Evidence: Skip's service binding, unsound and sound

Two one-file programs, each a framework binding and its use:

- [`framework-binding-unsound.ts`](../../examples/framework-binding-unsound.ts):
  today's binding. `createGraph`'s input type is a type parameter of its own,
  not tied to the declared inputs. At run time the runtime passes one
  collection per declared input. The service declares `input1` and reads
  `input2`, so it crashes at run time (`inputs.input2` is undefined), yet it
  type-checks.
- [`framework-binding-sound.ts`](../../examples/framework-binding-sound.ts):
  the binding made sound. `createGraph` obtains each collection through the
  definition that declared it (`inputs.get(definition)`), at that
  definition's types, so a collection exists only for a declared input.

Both files declare the runtime's interface in the file, so every checker reads
the same binding.

## Results

`reproduce.sh`, run at the commit that adds this directory, printed
[`results.txt`](results.txt):

| File | `tsc --strict` | pipeline (parser → OCaml → Lean) |
| ---- | -------------- | -------------------------------- |
| `framework-binding-unsound.ts` | accepts | verified (`main`) |
| `framework-binding-sound.ts` | accepts | verified (`main`) |

Under today's binding the crashing service passes both tools. The unsoundness
is in the binding, which describes the runtime wrongly, not in either
checker. Under the sound binding the service is verified. Its only way to a
collection is through a declared definition, so the crashing read cannot be
written: `tsc` itself refuses it.

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
