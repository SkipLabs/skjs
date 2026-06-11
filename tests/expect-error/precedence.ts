function testUnaryVsFunctionCall(): boolean {
  let foo = (): boolean => true;
  return !foo();
}

function testUnaryVsFunctionCallError(): void {
  let foo = (): boolean => true;
  // @skjs-expect-error This condition will always be true since this value is always defined
  // @ts-expect-error This expression is not callable
  let result = (!foo)();
}

function testUnaryVsMemberAccess(): boolean {
  let obj = { prop: true };
  return !obj.prop;
}

function testUnaryVsMemberAccessError(): void {
  let obj = { prop: true };
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  // @ts-expect-error Property 'prop' does not exist on this type
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
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  // @ts-expect-error Property 'met' does not exist on this type
  return (!obj).met();
}

function testArithmeticVsComparison(): boolean {
  return 1 + 2 < 3 + 4;
}

function testArithmeticVsComparisonError(): void {
  // @ts-expect-error Right operand of '+' is not assignable to the left operand's type
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
  // @skjs-expect-error A condition is expected to be of type boolean or a type with a single falsy value
  // @ts-expect-error Both operands of a comparison must have the same type
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
  // @skjs-expect-error The non-null assertion operator '!' is not allowed
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
