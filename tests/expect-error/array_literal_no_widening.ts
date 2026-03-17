// Tests demonstrating that removing literal widening from array literals
// does not lose expressiveness: ["toto", "titi"] is a subtype of both
// string[] and ("toto" | "titi")[], and commitment is exclusive.

// --- Helpers ---

function takesStringArray(values: string[]): void {
  const _first: string | undefined = values[0];
}

function takesLiteralUnionArray(values: ("toto" | "titi")[]): void {
  const _first: ("toto" | "titi") | undefined = values[0];
}

// --- Subtyping without widening ---

// ["toto", "titi"] is a subtype of string[].
function literalSubtypeOfStringArray(): void {
  const values: string[] = ["toto", "titi"];
  const _first: string | undefined = values[0];
}

// ["toto", "titi"] is a subtype of ("toto" | "titi")[].
function literalSubtypeOfLiteralUnionArray(): void {
  const values: ("toto" | "titi")[] = ["toto", "titi"];
  const _first: ("toto" | "titi") | undefined = values[0];
}

// --- Commitment exclusivity ---

// Once committed as string[], no longer ("toto" | "titi")[].
function committedAsStringArrayNotLiteralArray(): void {
  const values = ["toto", "titi"];
  takesStringArray(values);
  // @skjs-expect-error Invalid call
  takesLiteralUnionArray(values);
}

// Once committed as ("toto" | "titi")[], no longer string[].
function committedAsLiteralArrayNotStringArray(): void {
  const values = ["toto", "titi"];
  takesLiteralUnionArray(values);
  // @skjs-expect-error Invalid call
  takesStringArray(values);
}
