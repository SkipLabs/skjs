// tsc TS2440: an import binding that collides with a local declaration in
// the same declaration space is an error (merging happens through
// `declare module` augmentation, as in main.ts, not through a local
// redeclaration of an imported name).
// @ts-expect-error Import declaration conflicts with local declaration of 'Foo'.
import { Foo } from "./other";

interface Foo {
  c(): boolean;
}
