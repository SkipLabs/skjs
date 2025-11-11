// Demonstrates supported console APIs in SKJS.
function demoConsoleSurface(): void {
  console.log("Logging multiple values:", "alpha", 1, true);

  // console.assert accepts a condition plus an optional message.
  console.assert(true, "assertion should not fail");

  // console.error mirrors the variadic TypeScript signature.
  console.error("Error payload:", { code: 500 }, "fatal");
}

demoConsoleSurface();
