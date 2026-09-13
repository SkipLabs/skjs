// A successful constraint query must not survive growth of an unsealed
// inference candidate merely because an earlier call primed its cache.
// tsc --strict rejects these captured evolving arrays as implicit any[];
// SKJS instead tracks their element candidate. The call errors below assert
// SKJS's constraint check, not tsc's earlier implicit-any diagnostics.
function frozenNumbers<B extends () => number[]>(b: B): number[] {
  return b();
}

function primedThenWidened(): number[] {
  const a = [];
  a.push(1);
  const f = () => a;
  const first = frozenNumbers(f);
  // The first call establishes a number[] alias and seals its element type.
  // @skjs-expect-error Argument is not assignable to the parameter's type
  a.push("s");
  return frozenNumbers(f);
}

// Without the priming call, the same invalid relationship must also fail.
function widenedWithoutPriming(): number[] {
  const a = [];
  a.push(1);
  const f = () => a;
  a.push("s");
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return frozenNumbers(f);
}

// Repeated queries remain valid when later growth stays within the bound.
function primedStillNumbers(): number[] {
  const a = [];
  a.push(1);
  const f = () => a;
  const first = frozenNumbers(f);
  a.push(2);
  return frozenNumbers(f);
}
