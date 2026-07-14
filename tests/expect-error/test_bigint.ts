// Test file for bigint functionality

// Test bigint literals
const a: bigint = 123n;
const b: bigint = 9007199254740991n; // Number.MAX_SAFE_INTEGER
const c: bigint = BigInt("123");
const d: bigint = BigInt(456);

// Test bigint operations
const sum: bigint = a + b;
const diff: bigint = b - a;
const prod: bigint = a * 2n;
const quotient: bigint = b / a;
const remainder: bigint = b % a;

// Test comparison operations
const eq: boolean = a === 123n;
const neq: boolean = a !== b;
const lt: boolean = a < b;
const gt: boolean = b > a;
const lte: boolean = a <= 123n;
const gte: boolean = b >= a;

// Test type checking
const isBigInt: boolean = typeof a === "bigint";

// Test conversions
const strFromBigInt: string = a.toString();
const strFromBigIntWithRadix: string = a.toString(16);
const bigintValue: bigint = a.valueOf();

// Test BigInt constructor variations
const fromString: bigint = BigInt("999");
const fromNumber: bigint = BigInt(42);
const fromBoolean: bigint = BigInt(true);

// Test BigInt static methods (commented out for now - not supported)
// const asInt8: bigint = BigInt.asIntN(8, 300n);
// const asUint8: bigint = BigInt.asUintN(8, 300n);

// Test complex expressions
const complex: bigint = ((a + b) * (c - d)) / 2n;

// Test function that accepts bigint
function processBigInt(x: bigint): bigint {
  return x * 2n + 1n;
}

const result: bigint = processBigInt(a);

// Test template literals with bigint
const template: string = `The value is ${a} and doubled is ${a * 2n}`;

console.log("Basic bigint operations work!");
console.log("Sum:", sum);
console.log("Product:", prod);
console.log("Comparison:", lt);
console.log("Type check:", isBigInt);
console.log("String conversion:", strFromBigInt);
console.log("Template:", template);
