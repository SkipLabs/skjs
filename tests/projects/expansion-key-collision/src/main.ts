// Same-named aliases in different modules must not share an expansion-cache
// entry. The local `Box` is `{ n: number }`; dep's `Box` is `{ s: string }`.
import { get } from "./dep.js";

type Box = { n: number };

function unsoundCall(): string {
  const b: Box = { n: 1 };
  // @ts-expect-error Argument is not assignable to the parameter's type
  return get(b);
}

function localBoxStillWorks(): number {
  const b: Box = { n: 1 };
  return b.n;
}

function importedBoxStillWorks(): string {
  return get({ s: "ok" });
}

// Priming the imported expansion must not change the subsequent local type.
function importedFirst(): number {
  const text = get({ s: "ok" });
  const b: Box = { n: text.length };
  return b.n;
}

// Renaming a declaration must not change which flows are accepted.
type RenamedBox = { n: number };
function renamedControl(b: RenamedBox): string {
  // @ts-expect-error Argument is not assignable to the parameter's type
  return get(b);
}
