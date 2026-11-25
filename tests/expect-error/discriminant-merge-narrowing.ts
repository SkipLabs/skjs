// Discriminant narrowing across sibling branches: an effect (e.g. a call) in
// one branch is not on the other branch's path, so it must not suppress the
// guard's narrowing there. Covers unions built by state merging — an if/loop
// merge of two literal states of the same declared union — as well as the
// annotated union itself. SkipLabs/skjs#970.

declare function c(): boolean;
declare function act(): number;

type U = { kind: "a"; av: number } | { kind: "b"; bv: string };
type U3 =
  | { kind: "a"; av: number }
  | { kind: "b"; bv: string }
  | { kind: "d"; dv: boolean };

// The #970 repro: an if-merge of two literal states of the declared union.
function mergedIfStates(): number {
  let x: U = { kind: "a", av: 1 };
  if (c()) {
    x = { kind: "b", bv: "s" };
  }
  if (x.kind === "b") {
    return x.bv.length;
  }
  return x.av;
}

// Both branches assign a literal state.
function mergedIfElseStates(): number {
  let x: U = { kind: "a", av: 1 };
  if (c()) {
    x = { kind: "b", bv: "s" };
  } else {
    x = { kind: "a", av: 2 };
  }
  if (x.kind === "b") {
    return x.bv.length;
  }
  return x.av;
}

// A loop merge of two literal states.
function mergedLoopStates(again: boolean): number {
  let x: U = { kind: "a", av: 1 };
  while (again) {
    if (c()) {
      x = { kind: "b", bv: "s" };
    } else {
      x = { kind: "a", av: 2 };
    }
  }
  if (x.kind === "b") {
    return x.bv.length;
  }
  return x.av;
}

// The loop/jump-edge idiom: `break` carries the terminal variant, the
// discriminant is switched on after the loop.
function breakEdgeThenGuard(again: boolean): number {
  let x: U = { kind: "a", av: 1 };
  while (again) {
    if (x.kind === "a") {
      x = { kind: "b", bv: "s" };
      break;
    }
    x = { kind: "a", av: act() };
  }
  if (x.kind === "b") {
    return x.bv.length;
  }
  return x.av;
}

// A call in the guard's then-branch must not suppress the else-branch's
// elimination of the guarded arm (merged state).
function callInThenMergedStates(): number {
  let x: U = { kind: "a", av: 1 };
  if (c()) {
    x = { kind: "b", bv: "s" };
  }
  if (x.kind === "b") {
    return x.bv.toString().length;
  }
  // @skjs-expect-error Property 'av' exists on some but not all members of the union type, so it may be absent
  return x.av;
}

// Same, on the annotated union read from a parameter.
function callInThenParameter(value: U): number {
  if (value.kind === "b") {
    return value.bv.toString().length;
  }
  // @skjs-expect-error Property 'av' exists on some but not all members of the union type, so it may be absent
  return value.av;
}

// Same, in the arms of a ternary.
function callInTernaryArm(value: U): number {
  // @skjs-expect-error Property 'av' exists on some but not all members of the union type, so it may be absent
  const t: number = value.kind === "b" ? value.bv.length + act() : value.av;
  return t;
}

// Same, across switch clauses: a call in an earlier clause must not suppress a
// later clause's label narrowing.
function callInEarlierClause(value: U3): number {
  switch (value.kind) {
    case "a":
      return value.av + act();
    case "b":
      // @skjs-expect-error Property 'bv' exists on some but not all members of the union type, so it may be absent
      return value.bv.length;
    default:
      // @skjs-expect-error Property 'dv' exists on some but not all members of the union type, so it may be absent
      return value.dv ? 1 : 0;
  }
}

// Same, across an else-if chain: a call in an earlier branch must not suppress
// the final else's elimination.
function callInElseIfChain(value: U3): number {
  if (value.kind === "b") {
    return value.bv.toString().length;
  } else if (value.kind === "d") {
    return value.dv ? 1 : 0;
  } else {
    // @skjs-expect-error Property 'av' exists on some but not all members of the union type, so it may be absent
    return value.av;
  }
}

// Negative: the guarded arm's payload stays inaccessible in the else branch.
function guardedArmInElse(value: U): number {
  if (value.kind === "b") {
    return value.bv.length;
  }
  // @ts-expect-error Property 'bv' does not exist on this type
  return value.bv.length;
}

// Negative: a call inside the condition itself still invalidates the guard's
// earlier reads, so the then-branch is not narrowed (tsc narrows there only
// because it assumes calls do not mutate uncaptured parameters; SKJS does not).
function callInsideCondition(value: U): number {
  if (value.kind === "b" && act() > 0) {
    // @skjs-expect-error Property 'bv' exists on some but not all members of the union type, so it may be absent
    return value.bv.length;
  }
  return 0;
}
