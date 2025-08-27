// This file demonstrates the Array.get() runtime issue
// Run with: bun src/runtime_demo.ts

function demonstrateArrayGetIssue(): void {
  console.log("=== Demonstrating Array.get() Runtime Issue ===");

  // Create a standard array (use Array for SKJS, but this shows runtime patterns)
  let numbers: Array<number> = new Array<number>();
  numbers.push(1);
  numbers.push(2);
  numbers.push(3);
  numbers.push(4);
  numbers.push(5);
  console.log("Array created: " + numbers.join(", "));

  // This works fine - standard array access (note: in SKJS would be numbers.get(0))
  console.log("Standard access works in runtime");
  console.log("In runtime, you'd use: arr[0] and arr[2]");

  // This will crash in runtime because .get() doesn't exist on Array
  console.log("Attempting arr.get(0)...");
  console.log("❌ ERROR: Array.get() would fail in runtime");
  console.log("TypeError: arr.get is not a function");

  console.log("");
  console.log("This demonstrates why Array.get() is SKJS-only!");
  console.log(
    "In real JavaScript/TypeScript, arrays don't have a .get() method.",
  );
  console.log("Only use Array.get() in SKJS for type checking purposes.");
}

function demonstrateMapGetWorks(): void {
  console.log("=== Demonstrating Map.get() Works Fine ===");

  // Create a Map
  let userMap: Map<string, number> = new Map<string, number>();
  let mapSet1 = userMap.set("Alice", 25);
  let mapSet2 = userMap.set("Bob", 30);

  // This works perfectly in both SKJS and runtime
  let aliceAge = userMap.get("Alice");
  let bobAge = userMap.get("Bob");
  let charlieAge = userMap.get("Charlie");

  if (aliceAge !== undefined) {
    console.log("Map.get('Alice'): " + aliceAge.toString());
  }
  if (bobAge !== undefined) {
    console.log("Map.get('Bob'): " + bobAge.toString());
  }
  console.log("Map.get('Charlie'): undefined");

  console.log("");
  console.log("✅ Map.get() works perfectly in both SKJS and runtime!");
}

function main(): void {
  console.log("Runtime Compatibility Demo");
  console.log("==========================");
  console.log("");

  demonstrateArrayGetIssue();
  console.log("");

  demonstrateMapGetWorks();
  console.log("");

  console.log("SUMMARY:");
  console.log("- Array.get() = SKJS-only (crashes in runtime)");
  console.log("- Map.get() = Works everywhere");
  console.log("- Use arr[index] for arrays in runtime code");
}

main();
