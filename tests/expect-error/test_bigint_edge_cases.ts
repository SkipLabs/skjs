// Test edge cases and advanced bigint primitive methods

// Test toString with all valid radix values
const testValue: bigint = 255n;

// Binary (base 2)
const binaryStr: string = testValue.toString(2);

// Octal (base 8)
const octalStr: string = testValue.toString(8);

// Decimal (base 10, default)
const decimalStr: string = testValue.toString(10);
const defaultStr: string = testValue.toString();

// Hexadecimal (base 16)
const hexStr: string = testValue.toString(16);

// Base 36 (maximum supported radix)
const base36Str: string = testValue.toString(36);

// Test with very large numbers
const largeNumber: bigint =
  123456789012345678901234567890123456789012345678901234567890n;
const largeDecimal: string = largeNumber.toString();
const largeHex: string = largeNumber.toString(16);
const largeBinary: string = largeNumber.toString(2);

// Test with negative numbers
const negativeNumber: bigint = -987654321098765432109876543210n;
const negativeDecimal: string = negativeNumber.toString();
const negativeHex: string = negativeNumber.toString(16);
const negativeBinary: string = negativeNumber.toString(2);

// Test valueOf with various operations
const originalValue: bigint = 42n;
const valueOfResult: bigint = originalValue.valueOf();
const valueOfEquals: boolean = originalValue === valueOfResult;
const valueOfSameType: boolean = typeof originalValue === typeof valueOfResult;

// Test toLocaleString
const smallValue: bigint = 1234n;
const mediumValue: bigint = 1234567n;
const largeLocale: string = largeNumber.toLocaleString();
const smallLocale: string = smallValue.toLocaleString();
const mediumLocale: string = mediumValue.toLocaleString();
const negativeLocale: string = negativeNumber.toLocaleString();

// Test method chaining and combinations
const chainedOps: string = BigInt(1000).valueOf().toString(16);
const complexChain: boolean = BigInt("12345").valueOf() === BigInt(12345);

// Test with zero and edge values
const zero: bigint = 0n;
const one: bigint = 1n;
const minusOne: bigint = -1n;

const zeroStr: string = zero.toString();
const oneStr: string = one.toString();
const minusOneStr: string = minusOne.toString();

const zeroHex: string = zero.toString(16);
const oneHex: string = one.toString(16);
const minusOneHex: string = minusOne.toString(16);

const zeroLocale: string = zero.toLocaleString();
const oneLocale: string = one.toLocaleString();
const minusOneLocale: string = minusOne.toLocaleString();

// Test methods in arithmetic contexts
const toStringLength: number = largeNumber.toString().length;
const valueOfPlusOne: bigint = originalValue.valueOf() + 1n;
const valueOfTimesTwo: bigint = originalValue.valueOf() * 2n;

// Test methods in boolean contexts
const hasLongString: boolean = largeNumber.toString().length > 50;
const valueOfIsPositive: boolean = originalValue.valueOf() > 0n;
const negativeValueOfIsNegative: boolean = negativeNumber.valueOf() < 0n;

// Test methods with BigInt constructor combinations
const constructFromToString: bigint = BigInt(originalValue.toString());
const constructFromValueOf: bigint = BigInt(originalValue.valueOf().toString());

// Test comparison using method results
const comparison1: boolean =
  originalValue.toString() === valueOfResult.toString();
const comparison2: boolean =
  originalValue.valueOf() === BigInt(originalValue.toString());

// Test in template literals
const templateDecimal: string = `Decimal: ${largeNumber.toString()}`;
const templateHex: string = `Hex: ${largeNumber.toString(16)}`;
const templateBinary: string = `Binary: ${smallValue.toString(2)}`;
const templateLocale: string = `Locale: ${mediumValue.toLocaleString()}`;

// Test function using all methods
function analyzeNumber(value: bigint): void {
  const decimal: string = value.toString();
  const hex: string = value.toString(16);
  const binary: string = value.toString(2);
  const original: bigint = value.valueOf();
  const locale: string = value.toLocaleString();

  console.log("Analysis:");
  console.log("Decimal:", decimal);
  console.log("Hex:", hex);
  console.log("Binary:", binary);
  console.log("Original:", original);
  console.log("Locale:", locale);
}

// Test the analysis function
analyzeNumber(255n);
analyzeNumber(-255n);
analyzeNumber(0n);
analyzeNumber(9007199254740991n); // Number.MAX_SAFE_INTEGER equivalent

console.log("BigInt edge cases test completed!");
console.log("Large number decimal length:", toStringLength);
console.log("Chain result:", chainedOps);
console.log("Complex comparison:", complexChain);
console.log("Template results:", templateDecimal, templateHex);
