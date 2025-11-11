type Fn1 = (x: number) => number;
type Fn2 = (x: number | string) => number;

type FnUnion = Fn1 | Fn2;

const g: FnUnion = (x: number) => 1;

g(1);
g("oops");
