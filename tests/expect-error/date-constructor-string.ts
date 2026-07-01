// The Date constructor accepts a string (ISO date string) as its first
// argument. Before the stub was updated, `new Date(someString)` was falsely
// rejected because the first parameter was typed as `number | undefined`.

function test(): number {
  const d1: Date = new Date("2024-01-01T00:00:00Z");
  const d2: Date = new Date("2024-01-01");
  const d3: number = new Date("2024-01-01T00:00:00Z").getTime();
  // Numeric arguments still work.
  const d4: Date = new Date(2024, 0, 1);
  const d5: Date = new Date();
  return d3;
}
