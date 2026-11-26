// Omitting an optional field is rejected by design: skjs is intentionally
// stricter than tsc here (see tests/expect-error/objects.ts). A source value
// whose type lacks the optional field can still carry an excess property of
// that name with an unrelated type (width subtyping), so viewing it through the
// optional field would read that value at the wrong type. So a sub without the
// optional field (and no covering index) does not satisfy a super that declares
// it. tsc accepts all of these; skjs soundly rejects them.
interface Foo {
  readonly a: number;
  b?: string;
}

// @skjs-expect-error This class incorrectly implements 'Foo'
class ImplementsOmitting implements Foo {
  readonly a: number = 1;
}

function viaStructuralValue(x: { readonly a: number }): Foo {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function viaInstance(): Foo {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new ImplementsOmitting();
}

// ============================================================================
// #741: Freshly constructed instances (`new C()`) of fully-known classes
// ============================================================================

interface FooReadonly {
  readonly a: number;
  readonly b?: string;
}

const optSym: unique symbol = Symbol("optSym");

type FooReadonlySymbol = {
  readonly a: number;
  readonly [optSym]?: string;
};

class KnownClass {
  readonly a: number = 1;
}

class KnownChild extends KnownClass {
  readonly c: boolean = true;
}

abstract class KnownAbstractBase {
  readonly a: number = 1;
}

class KnownFromAbstract extends KnownAbstractBase {
  readonly c: boolean = true;
}

class GenericKnown<T> {
  readonly a: T;
  constructor(a: T) {
    this.a = a;
  }
}

// --- Positive cases: fresh `new C()` of a fully-known class ---

// Readonly omitted optional field: provably absent on exact `new KnownClass()`.
function freshKnownToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownClass();
}

function freshKnownChildToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownChild();
}

function freshKnownFromAbstractToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownFromAbstract();
}

function freshGenericKnownToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new GenericKnown(1);
}

// Readonly omitted optional symbol field: provably absent on exact `new KnownClass()`.
function freshKnownToReadonlyOptSymbol(): FooReadonlySymbol {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownClass();
}

// Fresh `new KnownClass()` satisfies Closed<KnownClass> and readonly-index
// supertypes when all fields match.
function freshKnownToClosed(): Closed<KnownClass> {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const c: Closed<KnownClass> = new KnownClass();
  return c;
}

function freshKnownToReadonlyIndex(): { readonly [k: string]: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownClass();
}

// Fresh `new KnownClass()` is still assignable to open `KnownClass`.
function freshKnownToOpenClass(): KnownClass {
  return new KnownClass();
}

// --- Negative cases: mutable omitted optional fields & mutable index ---

// Mutable omitted optional field MUST stay rejected even on fresh `new KnownClass()`:
// external code could write `f.b = "hi"` through `Foo`.
function freshKnownToMutableOpt(): Foo {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownClass();
}

function freshKnownToMutableIndex(): { [k: string]: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new KnownClass();
}

// --- Soundness boundary: open class types and `implements` MUST stay open ---
// TypeScript classes are open to subclassing (`extends`). A variable typed as
// `KnownClass` may hold a subclass adding `readonly b: number = 123`, so
// treating general `KnownClass` (or `implements FooReadonly`) as closed would
// let `b: number` be read as `string | undefined` at runtime!

class SubAddsIncompatibleB extends KnownClass {
  readonly b: number = 123;
}

function openClassParamToReadonlyOpt(x: KnownClass): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function subclassWitness(): FooReadonly {
  const b: KnownClass = new SubAddsIncompatibleB();
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return b;
}

function openClassToClosed(x: KnownClass): Closed<KnownClass> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// `implements` checks the class's instance type (open to subclasses), so
// omitting even a readonly optional field stays rejected.
// @skjs-expect-error This class incorrectly implements 'FooReadonly'
class ImplementsReadonlyOmitting implements FooReadonly {
  readonly a: number = 1;
}

// `in` narrowing on an open class parameter must NOT treat unknown keys as
// provably absent (`x` could be `SubAddsIncompatibleB`).
function inOnOpenClassStaysOpen(x: KnownClass): void {
  if ("b" in x) {
    // @skjs-expect-error Type of value is not assignable to the variable's type annotation
    const impossible: never = x;
  }
}

// --- Soundness boundary: ambient classes and ambient bases stay open ---

declare class AmbientBase {
  readonly a: number;
}

class ExtendsAmbient extends AmbientBase {
  readonly c: boolean = true;
}

declare namespace AmbientNs {
  class NestedAmbient {
    readonly a: number;
  }
}

class ExtendsNestedAmbient extends AmbientNs.NestedAmbient {
  readonly c: boolean = true;
}

function freshAmbientToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new AmbientBase();
}

function freshExtendsAmbientToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new ExtendsAmbient();
}

function freshExtendsNestedAmbientToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new ExtendsNestedAmbient();
}

// --- Soundness boundary: classes with declared index signatures stay open ---

class WithStringIndex {
  readonly a: number = 1;
  readonly [k: string]: number;
}

class WithNumberIndex {
  readonly a: number = 1;
  readonly [k: number]: number;
}

function freshWithStringIndexToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new WithStringIndex();
}

function freshWithNumberIndexToReadonlyOpt(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new WithNumberIndex();
}

// --- Private fields: must not leak through readonly index or optional fields ---

class WithPrivateField {
  readonly a: number = 1;
  private secret: number = 42;
}

function freshWithPrivateToReadonlyOptOtherKey(): FooReadonly {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new WithPrivateField();
}

function freshWithPrivateToSameNameOpt(): {
  readonly a: number;
  readonly secret?: string;
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new WithPrivateField();
}

function freshWithPrivateToReadonlyIndex(): { readonly [k: string]: number } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return new WithPrivateField();
}

function closedWithPrivateToReadonlyIndex(x: Closed<WithPrivateField>): {
  readonly [k: string]: number;
} {
  // Pre-fix bug: Left(f1) in isSub_NamedFields does not check f1.access
  // against idx2, allowing private fields to leak through an index signature.
  return x;
}
