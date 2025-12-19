// INCOMPLETENESS: Cannot subtract from top (unknown)
//
// This is a REPRESENTATION LIMITATION, not a missing implementation case.
// The clause ⟨∅ | ⊤⟩ (top) has no finite tag-set to subtract from.
// diff(⟨∅|⊤⟩, ⟨∅|{null,undefined}⟩) = ⟨∅|⊤⟩ (unchanged)
//
// Note: TypeScript's {} means "non-nullish top" (all values except null/undefined).
// In SKJS, {} means an empty object type (tag 9 only).
//
// See: docs/skjs-type-soundness.tex, Section 7.2

// PART 1: Typeof narrowing on unknown IS supported
function typeofNarrowingWorks(x: unknown): number {
  if (typeof x === "number") {
    return x; // OK: x narrowed to number
  }
  return 0;
}

// PART 2: Subtracting null/undefined from unknown is NOT supported
// This is a valid TypeScript program (--strictNullChecks) that SKJS rejects.
function nullCheckFails(x: unknown): {} {
  if (x !== null && x !== undefined) {
    // TypeScript: x narrowed to {} (non-nullish top)
    // SKJS: x still unknown (⊤ has no tags to subtract from)
    // @skjs-expect-error Invalid return type
    return x;
  }
  return {};
}

// Could be implemented: add excluded-tag or non-nullish flag to representation.
