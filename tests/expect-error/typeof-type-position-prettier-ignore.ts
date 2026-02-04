///////////////////////////////////////////////////////////////////////////////
// Improper typeof expressions - tests for invalid syntax
// These are in a separate file because prettier can't parse them
// (file matches *-prettier-ignore.* pattern)
///////////////////////////////////////////////////////////////////////////////

// Minimal declarations needed for tests
class Point {
  x: number;
  y: number;
  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
}

function sideEffectFunc(): number {
  return 42;
}

///////////////////////////////////////////////////////////////////////////////
// Literals - rejected by TypeScript
///////////////////////////////////////////////////////////////////////////////

// Number literal - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type NumberLiteralType = typeof 42;

// Number literal - function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testNumLiteralParam(x: typeof 42): number {
  return x;
}

// String literal - type alias context
// @skjs-expect-error TODO: typeof for complex expressions
type StringLiteralType = typeof "hello";

// String literal - function return type (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testStrLiteralReturn(): typeof "hello" {
  return "hello";
}

// Boolean literal - local variable annotation (TCEnv available)
// NOTE: Inside functions, expr() handles all expressions including literals
function testBoolLiteralLocal(): void {
  const x: typeof true = true;
}

// null literal (parsed as Var("null") so lookup fails)
// @skjs-expect-error Type null not found
type NullLiteralType = typeof null;

///////////////////////////////////////////////////////////////////////////////
// Function calls - rejected (side effects)
///////////////////////////////////////////////////////////////////////////////

// Function call - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type FuncCallType = typeof sideEffectFunc();

// Function call - function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testFuncCallParam(x: typeof sideEffectFunc()): number {
  return x;
}

// Method call - type alias context
// @skjs-expect-error TODO: typeof for complex expressions
type MethodCallType = typeof "hello".toUpperCase();

///////////////////////////////////////////////////////////////////////////////
// Binary/arithmetic expressions - rejected
///////////////////////////////////////////////////////////////////////////////

// Addition - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type AdditionType = typeof (1 + 2);

// Addition - function return type (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testAdditionReturn(): typeof (1 + 2) {
  return 3;
}

// Comparison
// @skjs-expect-error TODO: typeof for complex expressions
type ComparisonType = typeof (1 < 2);

///////////////////////////////////////////////////////////////////////////////
// new expressions - rejected
///////////////////////////////////////////////////////////////////////////////

// new expression - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type NewExprType = typeof new Point(1, 2);

// new expression - function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testNewExprParam(x: typeof new Point(1, 2)): Point {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Array literals - rejected
///////////////////////////////////////////////////////////////////////////////

// Array literal - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type ArrayLiteralType = typeof [1, 2, 3];

// Array literal - function return type (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testArrayLiteralReturn(): typeof [1, 2, 3] {
  return [1, 2, 3];
}

///////////////////////////////////////////////////////////////////////////////
// Object literals - rejected
///////////////////////////////////////////////////////////////////////////////

// Object literal - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type ObjectLiteralType = typeof { x: 1, y: 2 };

// Object literal - local variable annotation (TCEnv available)
// NOTE: Inside functions, expr() handles all expressions including object literals
function testObjectLiteralLocal(): void {
  const p: typeof { x: 1 } = { x: 1 };
}

///////////////////////////////////////////////////////////////////////////////
// Conditional/ternary expressions - rejected
///////////////////////////////////////////////////////////////////////////////

// Ternary - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type TernaryType = typeof (true ? 1 : 2);

// Ternary - function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testTernaryParam(x: typeof (true ? "a" : "b")): string {
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// this expression - context dependent
///////////////////////////////////////////////////////////////////////////////

// this in type alias - rejected (parsed as Var("this"), no this binding)
// @skjs-expect-error Type this not found
type ThisType = typeof this;

///////////////////////////////////////////////////////////////////////////////
// Template literals - rejected
///////////////////////////////////////////////////////////////////////////////

// Template literal - type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type TemplateLiteralType = typeof `hello`;

// Template with interpolation
// @skjs-expect-error TODO: typeof for complex expressions
type TemplateInterpType = typeof `value: ${42}`;

///////////////////////////////////////////////////////////////////////////////
// Parenthesized complex expressions - rejected
///////////////////////////////////////////////////////////////////////////////

// Parenthesized call - type alias (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type ParenCallType = typeof (sideEffectFunc());

// Parenthesized arithmetic - function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function testParenArithParam(x: typeof (2 * 3)): number {
  return x;
}
