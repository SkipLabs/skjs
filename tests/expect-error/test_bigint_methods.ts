// Test file for bigint primitive methods

// Test basic bigint creation
const bigintLiteral: bigint = 123456789012345678901234567890n;
const bigintFromString: bigint = BigInt("987654321098765432109876543210");
const bigintFromNumber: bigint = BigInt(42);
const bigintFromBoolean: bigint = BigInt(true);
const bigintFromBigInt: bigint = BigInt(bigintLiteral);

// Test toString method with different radices
const decimal: string = bigintLiteral.toString(); // Default base 10
const binary: string = bigintLiteral.toString(2);
const octal: string = bigintLiteral.toString(8);
const hexadecimal: string = bigintLiteral.toString(16);
const base36: string = bigintLiteral.toString(36);

// Test valueOf method
const valueOfResult: bigint = bigintLiteral.valueOf();

// Test toLocaleString method
const localeString: string = bigintLiteral.toLocaleString();

// Test arithmetic operations with method results
const arithmeticWithToString: string = "Result: " + bigintLiteral.toString();
const arithmeticWithValueOf: bigint = bigintLiteral.valueOf() + 1n;

// Test comparison operations with method results
const comparison1: boolean = bigintLiteral.valueOf() === bigintLiteral;
const comparison2: boolean = bigintLiteral.toString().length > 10;

// Test method chaining
const chainedResult: string = BigInt(999).valueOf().toString(16);

// Test with negative bigints
const negativeBigint: bigint = -123456789012345678901234567890n;
const negativeToString: string = negativeBigint.toString();
const negativeValueOf: bigint = negativeBigint.valueOf();
const negativeLocaleString: string = negativeBigint.toLocaleString();

// Test with zero
const zeroBigint: bigint = 0n;
const zeroToString: string = zeroBigint.toString();
const zeroValueOf: bigint = zeroBigint.valueOf();

// Test with one
const oneBigint: bigint = 1n;
const oneToString: string = oneBigint.toString();
const oneValueOf: bigint = oneBigint.valueOf();

// Test method calls in expressions
const expressionWithMethod: bigint =
  BigInt(42).valueOf() * 2n + BigInt("100").valueOf();
const stringExpressionWithMethod: string =
  "The value is: " + BigInt(123).toString(10);

// Test methods in conditionals
function testMethodsInConditionals(value: bigint): string {
  if (value.toString().length > 5) {
    return "Large number: " + value.toLocaleString();
  } else {
    return "Small number: " + value.toString();
  }
}

const conditionalTest1: string = testMethodsInConditionals(123n);
const conditionalTest2: string =
  testMethodsInConditionals(123456789012345678901234567890n);

// Test methods with template literals
const templateWithMethods: string = `Decimal: ${bigintLiteral.toString()}, Hex: ${bigintLiteral.toString(16)}`;

// Test function with bigint method calls
function processBigIntArray(): void {
  // Test array operations without const declarations
  const arr1: bigint = 1n;
  const arr2: bigint = 2n;
  const arr3: bigint = 3n;

  // Use methods on these values
  console.log(arr1.toString(), arr2.toString(), arr3.toString());
}

// Test function that creates bigint data
function createBigIntData(): void {
  const value: bigint = 42n;
  const decimal: string = BigInt(42).toString();
  const hex: string = BigInt(42).toString(16);
  const valueOfResult: bigint = BigInt(42).valueOf();

  console.log(
    "Value:",
    value,
    "Decimal:",
    decimal,
    "Hex:",
    hex,
    "ValueOf:",
    valueOfResult,
  );
}

// Test function that uses bigint methods
function formatBigInt(value: bigint, radix?: number): string {
  const stringValue: string = value.toString(radix);
  const localizedValue: string = value.toLocaleString();
  const originalValue: bigint = value.valueOf();

  return `String: ${stringValue}, Localized: ${localizedValue}, Original: ${originalValue.toString()}`;
}

const formattedResult1: string = formatBigInt(12345n);
const formattedResult2: string = formatBigInt(255n, 16);
const formattedResult3: string = formatBigInt(-9876543210n);

console.log("Bigint primitive methods test completed!");
console.log("Decimal:", decimal);
console.log("Binary:", binary);
console.log("Hex:", hexadecimal);
console.log("Formatted result:", formattedResult1);
console.log("Negative result:", negativeToString);
console.log("Template result:", templateWithMethods);
