// Basic function-based approach to avoid toplevel let
function basicTypesDemo(): void {
  // Basic variable declarations and type annotations
  let name: string = "Alice";
  let age: number = 25;
  let isActive: boolean = true;

  console.log(greet(name));
  console.log(add(10, 20).toString());
  console.log(multiply(6, 7).toString());
}

// Function declarations
function greet(name: string): string {
  return "Hello, " + name;
}

function add(a: number, b: number): number {
  return a + b;
}

// Arrow functions as function declarations
function multiply(a: number, b: number): number {
  return a * b;
}

// Run the demo
basicTypesDemo();
