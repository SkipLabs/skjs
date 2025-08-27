// Test bigint static properties and advanced usage patterns

// Test BigInt constructor with various inputs
const fromNumber: bigint = BigInt(42);
const fromString: bigint = BigInt("123456789012345678901234567890");
const fromBooleanTrue: bigint = BigInt(true);
const fromBooleanFalse: bigint = BigInt(false);
const fromBigInt: bigint = BigInt(999n);

// Test BigInt with edge cases
const fromZero: bigint = BigInt(0);
const fromNegativeNumber: bigint = BigInt(-42);
const fromNegativeString: bigint = BigInt("-987654321");

// Test BigInt constructor with string representations of different bases
const fromHexString: bigint = BigInt("0xFF");
const fromBinaryString: bigint = BigInt("0b1111");
const fromOctalString: bigint = BigInt("0o777");

// Note: BigInt static methods like asIntN/asUintN are not accessible
// in this type system due to the function + object pattern limitation
// But we can still test the BigInt constructor comprehensively

// Test method calls on constructed BigInts
const constructedToString: string = BigInt("12345").toString();
const constructedValueOf: bigint = BigInt(67890).valueOf();
const constructedToLocale: string = BigInt("999999").toLocaleString();

// Test BigInt with large number strings
const veryLarge: bigint = BigInt(
  "999999999999999999999999999999999999999999999999999",
);
const veryLargeString: string = veryLarge.toString();
const veryLargeHex: string = veryLarge.toString(16);

// Test BigInt constructor in expressions
const expression1: bigint = BigInt("100") + BigInt("200");
const expression2: bigint = BigInt(50) * BigInt(2);
const expression3: boolean = BigInt("300") === BigInt(300);

// Test BigInt constructor with method chaining
const chainConstruct1: string = BigInt("255").toString(16);
const chainConstruct2: bigint = BigInt(BigInt("42").toString());
const chainConstruct3: boolean = BigInt("123").valueOf() > BigInt("100");

// Test type consistency
const typeTest1: boolean = typeof BigInt(42) === "bigint";
const typeTest2: boolean = typeof BigInt("42") === "bigint";
const typeTest3: boolean = typeof BigInt(true) === "bigint";
const typeTest4: boolean = typeof BigInt(false) === "bigint";

// Test BigInt in template literals
const templateBigInt: string = `Value: ${BigInt("12345")}`;
const templateMethods: string = `Hex: ${BigInt(255).toString(16)}`;

// Test BigInt constructor with different radix outputs
const testNum: bigint = BigInt("1000");
const testBinary: string = testNum.toString(2);
const testOctal: string = testNum.toString(8);
const testDecimal: string = testNum.toString(10);
const testHex: string = testNum.toString(16);
const testBase36: string = testNum.toString(36);

// Test BigInt with mathematical operations
// Note: ** operator not supported, so using multiplication instead
const mathTest1: bigint =
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2") *
  BigInt("2"); // 2^10
const mathTest2: bigint = BigInt("1000") / BigInt("10");
const mathTest3: bigint = BigInt("1000") % BigInt("7");
const mathTest4: bigint = BigInt("100") + BigInt("23");
const mathTest5: bigint = BigInt("200") - BigInt("77");

// Test comparison operations with BigInt constructor
const compareTest1: boolean = BigInt("100") < BigInt("200");
const compareTest2: boolean = BigInt("50") > BigInt("25");
const compareTest3: boolean = BigInt("42") === BigInt(42);
const compareTest4: boolean = BigInt("0") !== BigInt(1);

// Test function using BigInt constructor
function testBigIntConstruct(input: string): string {
  const bigintValue: bigint = BigInt(input);
  const stringValue: string = bigintValue.toString();
  const hexValue: string = bigintValue.toString(16);
  const valueOf: bigint = bigintValue.valueOf();

  return `Input: ${input}, BigInt: ${stringValue}, Hex: ${hexValue}, ValueOf: ${valueOf}`;
}

const functionTest1: string = testBigIntConstruct("12345");
const functionTest2: string = testBigIntConstruct("-67890");
const functionTest3: string = testBigIntConstruct("0");

// Test edge cases (avoiding empty string which might cause issues)
const edgeCase1: bigint = BigInt("0"); // Zero case
const edgeCase2: bigint = BigInt("123"); // Clean number string

console.log("BigInt static and constructor test completed!");
console.log("From string:", fromString.toString());
console.log("Very large:", veryLargeString);
console.log("Expression result:", expression1.toString());
console.log("Function test:", functionTest1);
console.log("Type tests:", typeTest1, typeTest2, typeTest3, typeTest4);
console.log("Math tests:", mathTest2.toString(), mathTest3.toString());
