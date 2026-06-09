function testUnaryVsFunctionCall(): boolean {
  let foo = (): boolean => true;
  return !foo();
}

function testUnaryVsFunctionCallError(): void {
  let foo = (): boolean => true;
  // @skjs-expect-error Invalid call
  // @ts-expect-error Invalid !
  let result = (!foo)();
}

function testUnaryVsMemberAccess(): boolean {
  let obj = { prop: true };
  return !obj.prop;
}

function testUnaryVsMemberAccessError(): void {
  let obj = { prop: true };
  // @skjs-expect-error Unbound field: prop
  // @ts-expect-error Invalid !
  let result = (!obj).prop;
}

function testUnaryVsMethodCall(): boolean {
  let obj = {
    met(): boolean {
      return true;
    },
  };
  return !obj.met();
}

function testUnaryVsMethodCallError(): boolean {
  let obj = {
    met(): boolean {
      return true;
    },
  };
  // @skjs-expect-error Unbound field: met
  // @ts-expect-error Invalid !
  return (!obj).met();
}

function testArithmeticVsComparison(): boolean {
  return 1 + 2 < 3 + 4;
}

function testArithmeticVsComparisonError(): void {
  // @ts-expect-error Invalid + operand
  let result = 1 + (2 < 3) + 4;
}

function testLogicalVsComparison(): boolean {
  let a = 1,
    b = 2,
    c = 3,
    d = 4;
  return a < b && c < d;
}

function testLogicalVsComparisonError(): void {
  let a = 1,
    b = 2,
    c = 3,
    d = 4;
  // @skjs-expect-error Invalid comparison. Both operands must have the same type.
  // @ts-expect-error Invalid &&
  let result = a < (b && c) < d;
}

function testAssignmentVsLogical(): boolean {
  let x: number | boolean = 0;
  let a = true,
    b = false;
  // TODO: we actually cannot discriminate
  // x = (a || b)
  // (x = a) || b
  return (x = a || b);
}

function testPostfixVsMemberAccess(): string {
  let obj: { prop: string } | null = { prop: "hello" };
  // @skjs-expect-error Do not use the postfix ! operator
  return obj!.prop;
}

function testMultipleUnary(): boolean {
  let x = true;
  return !!x;
}

function testTernaryPrecedence(): number {
  let a = true;
  let n = 1;
  return a ? n + n : n * n;
}

function testAssignmentInTernary(): number {
  let x: number;
  let a = true,
    n = 10;
  // TODO: we actually cannot discriminate
  // x = (a ? n : n)
  // (x = a) ? n : n
  x = a ? n : n;
  return x;
}
