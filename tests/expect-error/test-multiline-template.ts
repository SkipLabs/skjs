const name: string = "Alice";
const age: number = 30;
const city: string = "New York";

// Multiline template literal without interpolation
const multilineSimple: string = `This is a
multiline template literal
that spans multiple lines`;

// Multiline template literal with interpolation
const multilineWithInterpolation: string = `Hello ${name},
You are ${age} years old and
you live in ${city}.
Welcome to our platform!`;

// Complex multiline template with expressions - now using direct expressions
const multilineComplex: string = `User Profile:
Name: ${name.toUpperCase()}
Age: ${(age + 5).toString()} (in 5 years)
Location: ${city}
Status: ${age >= 18 ? "Adult" : "Minor"}`;

// Template with indentation and mixed content
const htmlTemplate: string = `
<div class="user-card">
  <h2>${name}</h2>
  <p>Age: ${age.toString()}</p>
  <p>Location: ${city}</p>
</div>
`;
