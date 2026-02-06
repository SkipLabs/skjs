function closedObjectLiteralCanFlowToOptionalField(): void {
  const source = { b: 1 };
  const target: { a?: string } = source;
  const value: string = target.a ?? "";
  console.log(value);
}

function closedUnionCanFlowToOptionalField(): void {
  const cond = true;
  const source: { b: number } | { a: string } = cond
    ? { b: 1 }
    : { a: "ok" };
  const target: { a?: string } = source;
  const value: string = target.a ?? "";
  console.log(value);
}

function indexSignatureWithCompatibleValueCanFlowToOptionalField(): void {
  const source: { [k: string]: string | undefined } = {};
  const target: { a?: string } = source;
  const value: string = target.a ?? "";
  console.log(value);
}

function openObjectTopCannotFlowToOptionalField(): void {
  const source: {} = { a: 1 };
  // @skjs-expect-error Invalid annotation
  const target: { a?: string } = source;
  const value: string = target.a ?? "";
  console.log(value);
}

function unionWithObjectTopCannotFlowToOptionalField(): void {
  const cond = true;
  const open: {} = { a: 1 };
  const narrow: { a: string } = { a: "ok" };
  const source: {} | { a: string } = cond ? open : narrow;
  // @skjs-expect-error Invalid annotation
  const target: { a?: string } = source;
  const value: string = target.a ?? "";
  console.log(value);
}
