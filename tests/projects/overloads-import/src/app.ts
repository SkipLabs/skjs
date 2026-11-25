import { fmt } from "./lib.js";

// An imported overload group resolves first-match-wins, exactly as in the
// declaring file: each call picks the first matching overload signature.
function use(): void {
  const a: string = fmt("hi");
  const b: string = fmt(42);
}
