// Test file with only verified BigInt methods that actually exist in JavaScript

// Test BigInt constructor (verified to work)
const fromNumber: bigint = BigInt(42);
const fromString: bigint = BigInt("123456789012345678901234567890");
const fromBooleanTrue: bigint = BigInt(true);
const fromBooleanFalse: bigint = BigInt(false);
const fromBigInt: bigint = BigInt(999n);

// Test toString method with various radices (all verified)
const testValue: bigint = 255n;
const binaryStr: string = testValue.toString(2); // "11111111"
const octalStr: string = testValue.toString(8); // "377"
const decimalStr: string = testValue.toString(10); // "255"
const defaultStr: string = testValue.toString(); // "255"
const hexStr: string = testValue.toString(16); // "ff"
const base36Str: string = testValue.toString(36); // "73"

// Test valueOf method (verified)
const originalValue: bigint = 42n;
const valueOfResult: bigint = originalValue.valueOf();
const valueOfEquals: boolean = originalValue === valueOfResult;

// Test toLocaleString method (verified)
const largeNumber: bigint = 123456789012345678901234567890n;
const localeString: string = largeNumber.toLocaleString();
const smallLocale: string = testValue.toLocaleString();

// Test with negative numbers (all methods work with negatives)
const negativeValue: bigint = -987654321n;
const negativeDecimal: string = negativeValue.toString();
const negativeHex: string = negativeValue.toString(16);
const negativeLocale: string = negativeValue.toLocaleString();

// Test with zero and edge cases
const zero: bigint = 0n;
const one: bigint = 1n;
const minusOne: bigint = -1n;

const zeroStr: string = zero.toString();
const oneStr: string = one.toString();
const minusOneStr: string = minusOne.toString();

const zeroLocale: string = zero.toLocaleString();
const oneLocale: string = one.toLocaleString();
const minusOneLocale: string = minusOne.toLocaleString();

// Test method chaining (verified to work)
const chainedResult: string = BigInt(255).toString(16);
const chainedComparison: boolean = BigInt("12345").valueOf() === 12345n;

// Test in arithmetic expressions
const valueOfPlusOne: bigint = originalValue.valueOf() + 1n;
const valueOfTimesTwo: bigint = originalValue.valueOf() * 2n;

// Test in boolean expressions
const hasLongString: boolean = largeNumber.toString().length > 50;
const valueOfIsPositive: boolean = originalValue.valueOf() > 0n;

// Test in template literals
const templateDecimal: string = `Decimal: ${largeNumber.toString()}`;
const templateHex: string = `Hex: ${testValue.toString(16)}`;
const templateLocale: string = `Formatted: ${largeNumber.toLocaleString()}`;

// Test function using all verified methods
function analyzeBigInt(value: bigint): string {
  const decimal: string = value.toString();
  const hex: string = value.toString(16);
  const binary: string = value.toString(2);
  const original: bigint = value.valueOf();
  const formatted: string = value.toLocaleString();

  return `Dec: ${decimal}, Hex: ${hex}, Bin: ${binary}, Orig: ${original}, Fmt: ${formatted}`;
}

// Test the analysis function with various values
const analysis1: string = analyzeBigInt(255n);
const analysis2: string = analyzeBigInt(-255n);
const analysis3: string = analyzeBigInt(0n);
const analysis4: string = analyzeBigInt(9007199254740991n); // Number.MAX_SAFE_INTEGER as bigint

// Test BigInt constructor with string representations
const fromHex: bigint = BigInt("0xFF"); // Should be 255n
const fromBinary: bigint = BigInt("0b1111"); // Should be 15n
const fromOctal: bigint = BigInt("0o777"); // Should be 511n

// Test these constructed values
const hexAnalysis: string = fromHex.toString(16);
const binaryAnalysis: string = fromBinary.toString(2);
const octalAnalysis: string = fromOctal.toString(8);

// Test BigInt with large strings (verified to work)
const veryLarge: bigint = BigInt("999999999999999999999999999999999999999999");
const veryLargeFormatted: string = veryLarge.toLocaleString();
const veryLargeHex: string = veryLarge.toString(16);

// Test comparison operations using methods
const comparison1: boolean = BigInt("100").valueOf() < BigInt("200").valueOf();
const comparison2: boolean = fromHex.toString() === "255";
const comparison3: boolean = zero.valueOf() === 0n;

console.log("Verified BigInt methods test completed!");
console.log("Basic conversions:", binaryStr, hexStr, localeString);
console.log("Analysis:", analysis1);
console.log("Large number:", veryLargeFormatted);
console.log("Chain result:", chainedResult);
console.log("Template result:", templateHex);
console.log("Comparisons:", comparison1, comparison2, comparison3);
