# R2/R3c: snapshot-owned validation

**Executable architectural experiment. Not integrated into production SKJS.**
R2/R3c remain in progress; implementation status stays in
[skjs-improvement.md](../../docs/skjs-improvement.md). No native checker or
verification-calculus behavior is changed here.

## Read

- [DESIGN.md](DESIGN.md): original ownership, snapshot, replay, and publication
  protocol. The required-request ordering is corrected by the continuation below.
- [PROJECTION-PORT.md](PROJECTION-PORT.md): complete reference projection path,
  findings, inspected SKJS integration points, native acceptance criteria, and
  explicit remaining limits.

## Run

Python 3.10 or newer; no third-party dependencies:

```sh
python3 -m unittest discover -s experiment/validation-lifetime -v
python3 experiment/validation-lifetime/demo.py
python3 experiment/validation-lifetime/mutation_check.py
```

## What is implemented

`model.py` supplies immutable snapshots, original-operand judgments,
proposal-only clone replay, non-rewinding identities, transactional pending
requirements, read-only validation, and final owner retirement. A mandatory
materialization is now registered **before** evaluation, so a caught failure
cannot authorize publication of an empty journal.

`projection.py` carries opaque derived handles through resolved alias expansion,
known-array/tuple numeric projection, caching, subtype consumption, and final
publication. Symbolic elements remain symbolic. A frozen answer retains its
source equation, and a cache hit preserves the incoming derivation's prerequisites.
The validator never solves or seals a candidate to make its judgment succeed.

The combined suite passes **64 tests**: 27 original state-protocol tests, four
request-registration tests, and 33 projection-path tests. It includes 7,168
bounded state traces and 150 finite shape cases with independent finite-set
oracles. Five deliberate protocol mutations are detected by assertion failures.
A repeated-request test checks cache reuse without new validations or journal
entries; this is not a native SKJS performance result.

## Boundary

This is a reference implementation, not a port of `TEnv.numberIndexedType`.
The finite shape evaluator does not establish generic quantification, recursive
types, general index signatures, mutable-storage subtyping, or runtime effects.
Python private attributes stand in for enforced module capabilities. The
completeness of registered source premises remains a substantive obligation.

The Skip compiler and Docker were not available in the execution environment.
The native Skip build, full checker tests, and verifier suites were not run.
The next production deliverable is the bounded native path specified in
[PROJECTION-PORT.md](PROJECTION-PORT.md), with its actual regressions and cost
checks. Passing this experiment does not close R2/R3c.
