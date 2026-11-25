// Cross-file declaration merging, the tsc way: `Foo` is declared in
// other.ts and augmented here through a `declare module` block on the same
// module specifier. The two declarations merge into one interface, so
// members of both are visible.
import { Foo } from "./other";

declare module "./other" {
  export interface Foo {
    a(): string;
  }
}

function useFoo(f: Foo): void {
  const s: string = f.a();
  const n: number = f.b();
}
