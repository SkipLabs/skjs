// Cross-file declaration merging: `Foo` is declared both here and in
// other.ts (imported below); like tsc, the two declarations merge into one
// interface, so members of both are visible.
import { Foo } from "./other";

// @skjs-expect-error Duplicate class declaration 'Foo'
interface Foo {
  a(): string;
}

// @skjs-expect-error Duplicate class declaration 'Foo'
function useFoo(f: Foo): void {
  // @skjs-expect-error Property 'a' does not exist on this type
  const s: string = f.a();
  const n: number = f.b();
}
