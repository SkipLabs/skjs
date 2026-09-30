// repro for: expansion-key-collision (E-EXPKEY)
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// The expansion cache is keyed by bare name text + arguments (ExpansionKey),
// not by resolved definition. The local zero-arg alias Box expands first and
// fills the cache; the imported dep.ts Box (a different definition, same
// name text, same empty type arguments) then reuses that entry, so get's parameter
// checks against { n: number } instead of { s: string } and the call is
// accepted. At runtime get(b) reads b.s === undefined at static type string.
// With the local alias renamed (no collision) the same call is rejected:
// "The field 's' is missing".
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/expansion-key-collision BIN=target/host/dev/skjs
import { get } from "./dep.js";
type Box = { n: number };
function run(): string {
  const b: Box = { n: 1 };
  return get(b);
}
console.log(run());
