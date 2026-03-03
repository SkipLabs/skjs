interface BoxL<T> {
  value: T;
}
interface BoxR<T> {
  value: T;
}

declare function merge<A, B>(a: A, b: B): BoxL<A> & BoxR<B>;

declare function merge4<A, B, C, D>(
  a: A,
  b: B,
  c: C,
  d: D,
): (BoxL<A> & BoxR<B>) | (BoxL<C> & BoxR<D>);

// TInter collapses when both type args resolve to the same type.
function testConcrete(): void {
  const result = merge<number, number>(42, 42);
  const v: number = result.value;
}

// TInter collapses when both type args are the same union.
function testTypeParam<V, W>(v: V, w: W): void {
  const result = merge<V | W, V | W>(v, w);
  const x: V | W = result.value;
}

// Union of two intersections that each collapse independently.
function testDoubleCollapse<V>(v: V): void {
  const result = merge4<V, V, V, V>(v, v, v, v);
  const x: V = result.value;
}

// FIXME: SKJS treats { (): string } & { (): number } as never (incompatible
// call signatures), while TypeScript treats it as an overloaded callable.
// Before commit 520787bb, TObject#inter returned an empty TObject instead of
// None (bottom), keeping a phantom empty type in the union.
declare function getCallableInter(): ({ (): string } & { (): number }) | string;

function testCallableInter(): string {
  return getCallableInter();
}
