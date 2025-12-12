// INCOMPLETENESS: SKJS does not narrow unknown after null/undefined checks
//
// Root cause: diff(Top, nullish) = Top (unchanged)
// The diff operation returns Top unchanged when left.stypes = None.
//
// Note: TypeScript requires --strictNullChecks to narrow unknown to {}.

// PART 1: Typeof narrowing on unknown IS supported
function typeofNarrowingWorks(x: unknown): number {
  if (typeof x === "number") {
    return x;  // OK: x narrowed to number
  }
  return 0;
}

// PART 2: Null/undefined narrowing on unknown is NOT supported (the incompleteness)
// This is a valid TypeScript program that SKJS incorrectly rejects.
function nullCheckFails(x: unknown): {} {
  if (x !== null && x !== undefined) {
    // TypeScript (with --strictNullChecks): x is narrowed to {} here
    // SKJS: x is still unknown (diff cannot remove from Top)
    return x;  // SKJS ERROR: 'unknown' not assignable to '{}'
  }
  return {};
}

// This program is valid TypeScript (with --strictNullChecks) but rejected by SKJS.
