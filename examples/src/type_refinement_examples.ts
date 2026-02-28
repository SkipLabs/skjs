// Type Refinement Examples for SKJS
// Demonstrates the limitation that type refinement only works on locals

// Example 1: Null checks - correct pattern
function handleNullableString(obj: { message: string | null }): void {
  // Correct: assign to local variable first
  let message = obj.message;
  if (message !== null) {
    console.log(message.toUpperCase()); // Works: message is refined to string
  }
}

// Example 2: Union type refinement - correct pattern with ADT
type Response =
  | { kind: "success"; data: string }
  | { kind: "error"; message: string };

function processResponse(response: Response): void {
  // Correct: ADT pattern matching works directly
  if (response.kind === "success") {
    console.log("Success: " + response.data);
  } else if (response.kind === "error") {
    console.log("Error: " + response.message);
  }
}

// Example 3: Multiple property levels - correct pattern
function handleNestedObject(obj: {
  user: { name: string | null } | null;
}): void {
  // Correct: assign each level to locals
  let user = obj.user;
  if (user !== null) {
    let name = user.name;
    if (name !== null) {
      console.log("User name: " + name);
    }
  }
}

// Example 4: Complex union types - correct pattern
type APIResponse =
  | { kind: "success"; data: string }
  | { kind: "error"; message: string };

function handleAPIResponse(response: APIResponse): void {
  // Correct: works with ADT pattern matching
  if (response.kind === "success") {
    console.log("Data: " + response.data);
  } else if (response.kind === "error") {
    console.log("Error: " + response.message);
  }
}

// Example 5: Array element refinement - correct pattern
function processUsers(users: Array<{ name: string | null }>): void {
  // Correct: assign array elements to locals
  let firstUser = users[0];
  if (firstUser !== undefined) {
    let name = firstUser.name;
    if (name !== null) {
      console.log("First user: " + name);
    }
  }
}

// Example 6: Function parameter refinement - correct pattern
function processOptionalUser(user: { name: string; age: number } | null): void {
  // Correct: assign parameter to local for refinement
  let u = user;
  if (u !== null) {
    console.log("User: " + u.name + ", Age: " + u.age.toString());
  }
}

// Example 7: Boolean flag refinement - correct pattern
function handleConditionalData(obj: {
  hasData: boolean;
  data: string | null;
}): void {
  let hasData = obj.hasData;
  let data = obj.data;

  if (hasData && data !== null) {
    console.log("Data available: " + data);
  }
}

// Example 8: Numeric refinement - correct pattern
function processScore(result: { score: number | null; passed: boolean }): void {
  let score = result.score;
  let passed = result.passed;

  if (score !== null && passed) {
    console.log("Score: " + score.toString());
  }
}

// Main function to test all examples
function main(): void {
  console.log("Testing type refinement patterns...");

  // Test 1: Null checks
  handleNullableString({ message: "Hello World" });
  handleNullableString({ message: null });

  // Test 2: Union types with ADT pattern
  processResponse({ kind: "success", data: "success data" });
  processResponse({ kind: "error", message: "error message" });

  // Test 3: Nested objects
  // @skjs-expect-error Invalid call
  handleNestedObject({ user: { name: "Alice" } });
  handleNestedObject({ user: null });

  // Test 4: ADT pattern matching
  handleAPIResponse({ kind: "success", data: "test data" });
  handleAPIResponse({ kind: "error", message: "test error" });

  // Test 5: Array elements
  let users: Array<{ name: string | null }> = new Array<{
    name: string | null;
  }>();
  users.push({ name: "Bob" });
  users.push({ name: null });
  processUsers(users);

  // Test 6: Optional parameters
  processOptionalUser({ name: "Charlie", age: 30 });
  processOptionalUser(null);

  // Test 7: Boolean flags
  handleConditionalData({ hasData: true, data: "important data" });
  handleConditionalData({ hasData: false, data: null });

  // Test 8: Numeric values
  processScore({ score: 85, passed: true });
  processScore({ score: null, passed: false });

  console.log("Type refinement examples completed successfully!");
}

// Export for potential use in other modules
export {
  handleNullableString,
  processResponse,
  handleNestedObject,
  handleAPIResponse,
};
