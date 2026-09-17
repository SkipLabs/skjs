# Export snapshots

Small probe programs and, beside each, SKJS's exported claims for it printed
in the syntax the viewer shows: one line per parameter, result, statement
entry, expression, and closed subtype or expansion judgment, with every
unavailable type carrying the exporter's reason. They exist to make changes
to the exporter reviewable: a change shows as a diff in a `.snap` file, at
the site it affects.

The probes are chosen for what the exporter does with them, one phenomenon
each. They may use any TypeScript, including constructs outside the verified
fragment. The inferred-replacement probe also runs through the source pipeline
in `../inferred-replacement.mts`, reusing the same source to check distinct saved
local/field reads with both producers. `run.sh` exports all probes in one SKJS
run and `tests/export-snapshots.mts` compares. When a diff is intended, review it
and regenerate:

```sh
UPDATE_EXPECT=1 node verification/tests/export-snapshots.mts claims.json verification/tests/export-snapshots
```

The printed syntax is `printFull` in `tools/claim-text.mts`: the viewer's
surface syntax plus the parts it leaves out, so that two encodings that
differ never print the same.
