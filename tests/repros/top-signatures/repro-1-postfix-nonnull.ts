// Repro for SKJS: "Construction not supported: postfix operator !"
// Expected:
// - tsc: OK (non-null assertion is supported)
// - skjs: error "Construction not supported: postfix operator !"

function f(x: string | null): string {
  // non-null assertion
  return x!;
}


