// Test unary operators type checking

// Valid uses - these should pass type checking

// Test unary minus on numbers
const positiveNum: number = 42;
const negativeNum: number = -positiveNum;
const doubleNeg: number = -negativeNum;
const negLiteral: number = -100;

// Test unary plus on numbers
const plusNum: number = +42;
const plusNeg: number = +-42;
const plusVar: number = +positiveNum;

// Test unary bitwise NOT on numbers
const bitwiseNot: number = ~5;
const bitwiseNotNeg: number = ~-1;
const bitwiseNotVar: number = ~positiveNum;

// Test unary logical NOT on booleans
const trueVal: boolean = true;
const falseVal: boolean = !trueVal;
const doubleNot: boolean = !!trueVal;
// @skjs-expect-error This constant expression could have been simplified
const notLiteral: boolean = !false;
const notFalseVal: boolean = !falseVal;

// Test unary operators on bigints
const positiveBig: bigint = 100n;
const negativeBig: bigint = -positiveBig;
const bitwiseNotBig: bigint = ~positiveBig;
const negBigLiteral: bigint = -999n;

// Unary plus on bigints: '+' performs ToNumber, which throws on a bigint at
// runtime, so tsc rejects every occurrence with TS2736 ('-' and '~' stay
// valid).
// @skjs-expect-error Operator '+' cannot be applied to type 'bigint'
const plusBig: bigint = +positiveBig;

declare function acceptsBigIntArg(x: bigint): bigint;
function plusBigLiteralArg(): void {
  // @skjs-expect-error Operator '+' cannot be applied to type 'bigint'
  const r = acceptsBigIntArg(+100n);
}

function unionPlus(x: number | bigint): number | bigint {
  // @skjs-expect-error Operator '+' cannot be applied to type 'bigint'
  return +x;
}

// When the operand mixes a bigint with a type that is invalid for unary '+'
// in SKJS anyway, the tsc-aligned TS2736 diagnostic takes precedence over the
// generic invalid-operand one (tsc also reports only TS2736 here).
function mixedUnionPlus(x: string | bigint): void {
  // @skjs-expect-error Operator '+' cannot be applied to type 'bigint'
  const y = +x;
}

// Test unary operators in expressions
const expr1: number = -(10 + 5);
const expr2: number = ~(8 - 3);
const expr3: boolean = !(true && false);

// Test unary operators with type inference
function acceptsNumber(x: number): number {
  return x;
}

function acceptsBigInt(x: bigint): bigint {
  return x;
}

function acceptsBoolean(x: boolean): boolean {
  return x;
}

const testNum: number = acceptsNumber(-42);
const testBig: bigint = acceptsBigInt(-42n);
// @skjs-expect-error This constant expression could have been simplified
const testBool: boolean = acceptsBoolean(!true);
const testBool2: boolean = acceptsBoolean(!trueVal);
const testBitwise: number = acceptsNumber(~10);

// Invalid uses - these should fail type checking

// @skjs-expect-error Unary operator '-' cannot be applied to this type
const negString: number = -"hello";

// @skjs-expect-error Unary operator '-' cannot be applied to this type
const negBool: number = -true;

// @skjs-expect-error Unary operator '~' cannot be applied to this type
const bitwiseString: number = ~"test";

// @skjs-expect-error Unary operator '~' cannot be applied to this type
const bitwiseBool: number = ~false;

// @skjs-expect-error Operator '!' cannot be applied to this type
const notNumber: boolean = !42;

// @skjs-expect-error Operator '!' cannot be applied to this type
const notString: boolean = !"hello";

// @skjs-expect-error Unary operator '+' cannot be applied to this type
const plusString: number = +"world";

// @skjs-expect-error Unary operator '+' cannot be applied to this type
const plusBool: number = +false;
