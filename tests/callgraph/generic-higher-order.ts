// Tests that the transitive closure is sound when function types flow
// through a generic with a contravariant TVar position: double and
// triple both flow into V, and apply (which calls its Callback
// argument) flows into f: (x: V) => void.
//
// foo does not call double, but fn:double is in the dependency graph
// of fn:foo because double is passed at the same type as triple,
// which is called, and the dependency analysis abstracts function
// parameters by their type.

type Callback = (x: number) => void;

function double(x: number): void {}

function triple(x: number): void {}

function apply(f: Callback): void {
  f(1);
}

function foo<V>(a: V, f: (x: V) => void, b: V): void {
  f(b);
}

// @skjs-callgraph-full
// arrow-annot: fn:apply, fn:double, fn:triple
// fn:apply: arrow-annot
// fn:foo: arrow-annot
// fn:test: fn:foo
//
// @skjs-callgraph-closure
// fn:double: fn:foo
// fn:triple: fn:foo
function test(): void {
  foo(double, apply, triple);
}
