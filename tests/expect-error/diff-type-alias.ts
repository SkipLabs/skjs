// Test that TType::diff correctly expands type aliases before computing set differences.
//
// The diff operation computes an over-approximation of left \ right.
// Without expanding type aliases, diff sees only the alias name, not its contents.
// For example, diff(MaybeNumber, undefined) must expand MaybeNumber to
// (number | undefined) to recognize that undefined can be subtracted.
//
// These tests use destructuring defaults as a concrete scenario where diff is called:
// const { f = defaultValue } = x; computes diff(fieldType, undefined) to determine
// the type of f when the default is used.

// ============================================================================
// SECTION 1: Basic type alias expansion
// ============================================================================

type MaybeNumber = number | undefined;
type MaybeString = string | undefined;
type NestedMaybe = MaybeNumber | string;

// Baseline: When the union is written inline, diff sees its structure directly.
function testInline(x: { f: number | undefined }): number {
  const { f = 1 } = x;
  return f;
}

// When the same union is behind a type alias, diff must expand it first.
function testAlias(x: { f: MaybeNumber }): number {
  const { f = 1 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// Nested type aliases must be fully expanded to reveal the complete union.
function testNestedAlias(x: { f: NestedMaybe }): number | string {
  const { f = "" } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// ============================================================================
// SECTION 2: Multiple aliases in a union
// ============================================================================

type MaybeNumberOrString = MaybeNumber | MaybeString;

// When a union contains multiple type aliases, each must be expanded.
function testMultipleAliases(x: { f: MaybeNumberOrString }): number | string {
  const { f = "" } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// ============================================================================
// SECTION 3: Aliases built from other aliases
// ============================================================================

type NumberOnly = number;
type StringOnly = string;
type NumberOrStringOrUndefined = NumberOnly | StringOnly | undefined;

// An alias built from other aliases still requires full expansion.
// NumberOrStringOrUndefined references NumberOnly and StringOnly,
// which must all be expanded to reveal the complete union structure.
function testAliasWithUndefinedInside(x: {
  f: NumberOrStringOrUndefined;
}): number | string {
  const { f = 0 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// ============================================================================
// SECTION 4: Deeply nested alias structures
// ============================================================================

type DeepNested = MaybeNumber | NestedMaybe;

// Aliases that reference other aliases must be recursively expanded.
// DeepNested -> MaybeNumber, NestedMaybe -> MaybeNumber -> (number | undefined)
function testDeepNested(x: { f: DeepNested }): number | string {
  const { f = 0 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// ============================================================================
// SECTION 5: Optional fields with type aliases
// ============================================================================

// Baseline: Optional fields without type aliases work (union structure is visible).
function testOptionalBaseline(x: { f?: number }): number {
  const { f = 1 } = x;
  return f;
}

// When an optional field uses a type alias, the alias must still be expanded
// even though the optional marker also contributes to the union.
function testOptionalWithMaybeAlias(x: { f?: MaybeNumber }): number {
  const { f = 1 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

// ============================================================================
// SECTION 6: Type aliases with multiple nullable types
// ============================================================================

type MaybeNullOrUndefined = number | null | undefined;

// Alias expansion must preserve all union members, not just the subtracted one.
// Here null must remain after undefined is subtracted.
function testNullPreserved(x: { f: MaybeNullOrUndefined }): number | null {
  const { f = 1 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}

type MaybeNullAlias = number | null;
type MaybeNullUndefinedAlias = MaybeNullAlias | undefined;

// Nested aliases with multiple nullable types must all be expanded correctly.
function testNullAliasPreserved(x: {
  f: MaybeNullUndefinedAlias;
}): number | null {
  const { f = 1 } = x;
  // @skjs-expect-error Invalid return type
  return f;
}
