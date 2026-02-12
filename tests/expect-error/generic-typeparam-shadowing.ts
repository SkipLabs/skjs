type Box<T> = { value: T };
type ArrBox<T> = Array<T>;

class CBox<T> {
  value: T;

  constructor(value: T) {
    this.value = value;
  }
}

declare function fooBoxS<S extends Box<number>>(x: S): S;
declare function fooBoxT<T extends Box<number>>(x: T): T;
declare function fooArrS<S extends ArrBox<number>>(x: S): S;
declare function fooArrT<T extends ArrBox<number>>(x: T): T;
declare function fooClassS<S extends CBox<number>>(x: S): S;
declare function fooClassT<T extends CBox<number>>(x: T): T;

function mkBoxNumber(): Box<number> {
  let n: number = 42;
  return { value: n };
}

function testS(): void {
  const b = mkBoxNumber();
  const r: Box<number> = fooBoxS(b);
  console.log(r.value);
}

function testT(): void {
  const b = mkBoxNumber();
  const r: Box<number> = fooBoxT(b);
  console.log(r.value);
}

function testArrayShadowing(): void {
  const a: number[] = [1, 2, 3];
  const r1: number[] = fooArrS(a);
  const r2: number[] = fooArrT(a);
  r1.push(4);
  r2.push(5);
}

function testClassShadowing(): void {
  const c: CBox<number> = new CBox(42);
  const r1: CBox<number> = fooClassS(c);
  const r2: CBox<number> = fooClassT(c);
  console.log(r1.value + r2.value);
}
