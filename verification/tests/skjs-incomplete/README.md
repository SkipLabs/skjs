# SKJS incompleteness examples

Programs rejected by SKJS whose declared types are true. These are precision
gaps, not unsafe programs. In most of them the independent verifier establishes
the result after the producer’s claims are repaired; where it does not, the entry
below says so, since being rejected by a checker whose annotation holds is what
makes an example belong here, and what today’s rules can certify is a separate
fact.

## The repairs kept beside them

Six of these carry a `.candidate.json` next to the source: a claim set the
verifier establishes, checked, so the reader shows it on opening rather than
leaving the repair to be rediscovered by hand each time.

| source | the repair |
|---|---|
| `negated-loop-exit.ts` | the claims TypeScript's own checker states |
| `singleton-negation.ts` | the same |
| `null-loop-exit.ts` | the same |
| `arrow-intersection.ts` | the same |
| `write-refined-read.ts` | a current-content assertion at the return entry |
| `empty-domain-escape.ts` | the closure claimed as what it is, subsumed at the edge |

The first four need nothing invented: where SKJS's claims do not verify and the
other producer's do, the second producer's claims *are* the repair, and saying
so is what a two-producer corpus is for.

The last two are the interesting ones, because neither producer can state them.

`write-refined-read.ts` needs the assertion this file's own comment names:
`cell` holds exactly `true` after the write, independently of its persistent
Boolean invariant. SKJS's export forgets it and the TypeScript producer states
no current-content assertions at all, so neither can express the repair even
though the claim is true and the verifier derives it. The reader prints such a
claim as `{ value: boolean = (true) }`.

`empty-domain-escape.ts` shows that *where* a claim sits decides whether a rule
can apply. `Arrow.empty` — an arrow with an empty domain is above every arrow —
is in the checker's rules (`PositiveRules.lean`) and the producer tries it
first. Claiming the closure expression itself as `(never) => boolean` still
fails, because that asks for the body to be typed against `boolean` under an
uninhabited parameter. Claim the closure as `(null) => null`, what it actually
is, and let the edge into the statement entry do the subsumption: same program,
same rules, same declared type, and it verifies.

`undefined-completes.ts` carries no draft because it needs none: SKJS rejects
the program and its own partial export already establishes it.

Opening one of these in the reader shows `·→✓`: the producer column is `·`
because the claims on screen are not its, and the proof column is `✓` because
they check. **Restore the producer's claims** shows what the producer said,
which is the finding the fixture exists for; it leaves the file alone, because
a repair belongs to the tree rather than to one session.

A draft is about one exact source, so touching a source makes its draft stale.
The reader then says so and falls back to the producer's claims, and the `Kept
drafts` suite fails — re-derive the draft against the source as it is, rather
than editing the hash.

`negated-loop-exit.ts` demonstrates incompleteness, not unsoundness. SKJS rejects
its `true` return annotation because it forgets the condition's false edge after
`while (!flag)`. The function returns true for both Boolean inputs: the loop body
returns true, and reaching the following return entails `flag = true`.

`negation.mts` takes SKJS's normal-mode partial export (without `--keep-going`).
The original broad exit claim does not suffice under local verification. The test
independently checks an explicit repair of the final binding and expression to
true and rejects an incorrect false exit binding. No SKJS behavior is changed.

`singleton-negation.ts` is another producer precision gap: SKJS types `!flag` as
`boolean` even for `flag : true`. Changing just that expression claim to `false`
makes its declared `false` result independently verifiable. The `ifKnown` rule
checks the condition's singleton type before selecting the false-valued arm;
the test rejects the opposite claimed result. Normal partial collection suffices.

`null-loop-exit.ts` isolates the same issue for `while (value === null) { continue; }`.
For Boolean inputs the loop is skipped; null diverges. Reaching the return therefore
implies a Boolean value. SKJS rejects it. `null-tests.mts` repairs the final entry
binding and returned-expression claim to `boolean`, independently checks the
certificate, and rejects an opposite null exit refinement. No keep-going export
or termination claim is involved.

`write-refined-read.ts` records a post-write precision gap. The function assigns
`true` to a Boolean cell and returns its current contents. It always returns true;
SKJS rejects the singleton result annotation, whereas TypeScript accepts it.
Normal first-error collection records the final read as `boolean`.

[WriteRefinedRead.lean](../../lean/Verification/ExperimentState/WriteRefinedRead.lean)
proves the modeled body safe at true and separately proves its terminating
execution. [Program typing](../../PROGRAM-TYPING.md#current-content-rules-semantic-layer)
documents the rules used by that proof.

The original broad return-entry claim does not verify locally: it forgets the
write's current-true fact. An explicit candidate with `{ value: boolean = true }`
at that entry verifies, even if the read's expression claim stays Boolean. The
incoming write edge justifies the observation and the return statement uses it
locally. False entry or read claims fail. `write-observations.mts` checks these
outcomes, the source shape, and runtime and producer behavior. The three unsafe
original exports are independently audited by `refinement-witnesses.mts`.

`undefined-completes.ts` is the one entry the verifier establishes with no
repair at all. A body that completes returns undefined, which is what it
declares; SKJS rejects it as not returning on every path. The exit carries
undefined and discharges the annotation directly, so the producer's partial
export is enough. `skjs-unsound/never-completes.ts` is the same SKJS check
skipped rather than too strict.

`arrow-intersection.ts` is a precision gap in the type algebra rather than in a
refinement. `TFun::inter` computes the intersection of two function types as
whichever is a subtype of the other, and as `never` when neither is, so a
function meeting both signatures is refused as "not assignable to type 'never'"
and keep-going collection exports the binding at the empty type. TypeScript
accepts the program, which returns null as declared. The verifier lowers the
intersection to one arrow row with both signatures, proves the lambda under
each and resolves the call to the first signature admitting its argument;
`source-claims.mts` verifies the fixture from handwritten claims that state the
intersection as the source declares it, and rejects a body that meets only one
signature. The producer's own export cannot be repaired into this: the claim
it would need is the one it computes as empty. The same collapse taken as an
assumption is `skjs-unsound/arrow-intersection.ts`.
