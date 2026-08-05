// Abstract evaluation of individual expression forms. The report shows each
// function's return value, so each form below is exposed as one.
//
// `typeof` on a tracked primitive folds exactly, as does `void e` and the old
// value of a postfix `++`. A conditional whose branches agree folds to their
// join even when the condition is unknown, and a conditional whose condition is
// unknown still walks *both* branches, so calls appearing only there resolve.

function typeofNumber(): string {
  return typeof 5;
}

function typeofString(): string {
  const s = "a";
  return typeof s;
}

function typeofNull(): string {
  // The historical wart: `typeof null === "object"`.
  return typeof null;
}

function typeofIsNumber(): boolean {
  return typeof 5 === "number";
}

function voidValue(): undefined {
  return void 0;
}

function postIncrement(): number {
  let i = 5;
  // Postfix `++` evaluates to the *old* value.
  return i++;
}

function inThen(): number {
  return 1;
}

function inElse(): number {
  return 2;
}

function pick(flag: boolean): number {
  // `pick` is called with both `true` and `false`, so `flag` joins to top and
  // neither branch is pruned; both are walked, so `inThen` and `inElse` are
  // each analyzed and `pick` returns their join, top.
  return flag ? inThen() : inElse();
}

function agree(flag: boolean): number {
  // The condition is unknown for the same reason, but both branches yield 7.
  return flag ? 7 : 7;
}

function main(): number {
  const a = typeofNumber();
  const b = typeofString();
  const c = typeofNull();
  const d = typeofIsNumber();
  const e = voidValue();
  const f = postIncrement();
  const g = pick(true) + pick(false);
  const h = agree(true) + agree(false);
  return f + g + h;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
