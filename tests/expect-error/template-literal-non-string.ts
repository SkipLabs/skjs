const name: string = "Alice";
const age: number = 30;
const active: boolean = true;

// Function that returns an object (not stringifiable)
function getObj(): { foo: string } {
  return { foo: "bar" };
}

// @ts-expect-error
const invalidObjectTemplate: string = `Object: ${getObj()}`;

// Valid templates - should work with complex expressions now!
const validStringTemplate: string = `Hello ${name}, you are great!`;
const validNumberTemplate: string = `Age: ${age}`;
const validBooleanTemplate: string = `Active: ${active}`;

// Complex expressions that should now work
const complexTemplate: string = `Name: ${name.toUpperCase()}, Age in 5 years: ${age + 5}`;
const conditionalTemplate: string = `Status: ${age >= 18 ? "Adult" : "Minor"}`;

// Multiline template literal
const multilineTemplate: string = `This is a
multiline template with ${name.toLowerCase()}
spanning multiple lines`;
