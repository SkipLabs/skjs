const name: string = "Alice";
const age: number = 30;
const active: boolean = true;

// Function that returns an object (not stringifiable)
function getObj(): { foo: string } {
  // @skjs-expect-error Invalid return type
  return { foo: "bar" };
}

// @skjs-expect-error Template literal expressions must be string, number, bigint, boolean, null, or undefined
const invalidObjectTemplate: string = `Object: ${getObj()}`;

// Valid templates with various expression types
const validStringTemplate: string = `Hello ${name}, you are great!`;
const validNumberTemplate: string = `Age: ${age}`;
const validBooleanTemplate: string = `Active: ${active}`;

// Complex expressions in templates
const complexTemplate: string = `Name: ${name.toUpperCase()}, Age in 5 years: ${age + 5}`;
const conditionalTemplate: string = `Status: ${age >= 18 ? "Adult" : "Minor"}`;

// Multiline template literal
const multilineTemplate: string = `This is a
multiline template with ${name.toLowerCase()}
spanning multiple lines`;
