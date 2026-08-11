# Unsound: `subst.seenSub` memoizes judgements made on unsealed candidate bounds during freeze windows (order-dependent acceptance)

Proposed labels: `soundness`, `bug`, `inference`, `caching`. Related:
PR #446 (partial fix this is the residual of), PRs #713/#721/#740 (the
freeze design that created the residual).

## Summary

During a constraint-admissibility check (`freezeCandidates` window in
`growTVars`), `Subst::get` covariant on an open *candidate* returns its
bound **without sealing**. A successful `isSub` in that window is memoized
in `subst.seenSub`, which is keyed only by the type pair — not by the
substitution version — and a TVar hashes by id, not binding. If the
candidate later grows, the memo records a judgement that no longer holds and
is reused without re-validation. The result is **order-dependent acceptance**:
adding an *earlier* call to a generic function flips a correct rejection
into an unsound acceptance.

The same freeze-window write path exists for `seenInter` (reached via the
constraint-application loop in `Subst::get` → `TType::inter`); it is
exercised by the witness below but was not isolable from `seenSub`'s
contribution. The fix below covers both.

## Minimal reproduction (self-contained)

Reproduction: [`repros/freeze-window-stale-seensub.ts`](repros/freeze-window-stale-seensub.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/freeze-window-stale-seensub.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics**.
- Decisive order-dependence control: the identical program **without the
  priming `r0 = g(f)` call** (widen first, then a single `g(f)`) is
  **rejected** with a proper contravariance error. Adding the earlier call
  flips the verdict.
- Runtime: `m : number` holds the string `"s"`.

## Root cause

- Unsealed freeze read: `src/TTypeSubst.sk:218-227` (`freezeCandidates &&
  isCandidate` arm of `get`).
- Pair-keyed memo write on success: `src/TTypeSubtyping.sk:1837-1841`
  (`subst.seenSub`); contrast `tenv.seenSub` at :1852, which *is*
  version-keyed.
- The freeze flag lives outside `SubstState` (`src/TTypeSubst.sk:89`), so no
  save/restore erases memos written under it.
- `seenInter` shares the shape: write at `src/TTypeInter.sk:123`, reachable
  under freeze via the constraint loop `src/TTypeSubst.sk:237-239`.

## Relation to existing issues/PRs

PR #446 fixed stale caches surviving save/restore and version-keyed
`tenv.seenSub`, but left `subst.seenSub` (and `seenInter`) pair-keyed,
relying on save/restore — which the freeze-window write-site-suppression
design (PRs #713/#721/#740) deliberately bypasses. This is the uncovered
residual. Regression test for the original bug:
`tests/expect-error/seensub-stale-cache.ts`. Not previously tracked.

## Suggested fix

Version-key `subst.seenSub` and `seenInter` (as PR #446 did for
`tenv.seenSub`), or suppress memo *writes* while `freezeCandidates` is set.

## Provenance

Deep dives E (`docs/deep-dives/subst-state-discipline.tex`, MR-1) and B
(`docs/deep-dives/lattice-operations.tex`, C-FREEZE-CACHE); witness
constructed during adversarial verification 2026-07-05. Main-paper
obligation affected:
Monotone Reads Under Growth.
