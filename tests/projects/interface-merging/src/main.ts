// Cross-file declaration merging: `Foo` is declared both here and in
// other.ts (imported below); like tsc, the two declarations merge into one
// interface, so members of both are visible.
import { Foo } from "./other";

interface Foo {
  a(): string;
}

function useFoo(f: Foo): void {
  const s: string = f.a();
  const n: number = f.b();
}
