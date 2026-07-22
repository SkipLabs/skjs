---
name: False rejection
about: SKJS rejects a program that tsc --strict accepts and that is safe at runtime
title: "False positive: "
labels: false-positive
---

**Minimal repro (`.ts`)**

```ts
```

**What SKJS does**: rejects with `<the diagnostic>`.

**Expected**: accepted — this is within the supported subset (see [`skjs-rules.md`](../../skjs-rules.md)).

**`tsc --strict --noEmit` output** (should be clean):

**Version**: output of `skjs --version` (or the commit SHA).
