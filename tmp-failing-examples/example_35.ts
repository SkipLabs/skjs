// (1) Function union: not callable unless domains match.
type F = ((x: number) => string) | ((x: string) => string);
declare const f: F;
f(1);      // ERROR (both TS strict and SKJS)

// (2) Generic wrapper that forces a single domain -> never-inference.
const both = <A>(p: (a: A) => void, q: (a: A) => void) => (a: A) => { p(a); q(a); };
declare const h: ((x: number) => void) | ((x: string) => void);
const combo = both(h, h);
// combo has type (a: never) => void; calling it is impossible.
// @expect-error
combo(42);

// (3) Safe overriding uses generics (no parameter narrowing).
class B<E extends Event = Event> { handle(e: E): void {} }
class C extends B<MouseEvent> { handle(e: MouseEvent): void {} }

// (4) Refinement cannot recover from never-inference.
const g = both(h, h);
g as (a: never) => void;  // document the collapsed domain explicitly
