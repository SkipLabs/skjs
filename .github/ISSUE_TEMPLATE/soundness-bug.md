---
name: Soundness bug (unsound accept)
about: SKJS accepts a program that would fail at runtime for type reasons
title: "Unsound: "
labels: soundness
---

**Minimal repro (`.ts`)**

```ts
// the smallest program SKJS accepts but shouldn't
```

**What SKJS does**: accepts with no error.

**Expected**: the diagnostic that should fire, or the runtime failure the program would hit.

**`tsc --strict --noEmit` output** (if relevant):

**Version**: output of `skjs --version` (or the commit SHA).
