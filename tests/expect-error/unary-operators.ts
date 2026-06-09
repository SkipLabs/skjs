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
// @skjs-expect-error Constant expression could have been simplified
const notLiteral: boolean = !false;
const notFalseVal: boolean = !falseVal;

// Test unary operators on bigints
const positiveBig: bigint = 100n;
const negativeBig: bigint = -positiveBig;
const bitwiseNotBig: bigint = ~positiveBig;
const negBigLiteral: bigint = -999n;

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
// @skjs-expect-error Constant expression could have been simplified
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

// @ts-expect-error Invalid unary !
const notNumber: boolean = !42;

// @ts-expect-error Invalid unary !
const notString: boolean = !"hello";

// @skjs-expect-error Unary operator '+' cannot be applied to this type
const plusString: number = +"world";

// @skjs-expect-error Unary operator '+' cannot be applied to this type
const plusBool: number = +false;
