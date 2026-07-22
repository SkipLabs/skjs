// An `if` branch that cannot complete normally is not a path out of the `if`:
// a return/throw branch never re-joins, and a break/continue branch re-joins
// after the enclosing switch or loop — through its jump edge, which already
// carries the state at the jump. Merging such a branch's scope into the code
// after the `if` adds a path that cannot happen there.

// The break sub-path's write travels its jump edge to the post-switch merge —
// it does not leak through the `if` into the clause fallen into, which is
// reached only with `y` still "a" (the else path) or "b" (its own label).
function breakSubpathWriteStaysOnItsEdge(
  y: "a" | "b" | "c",
  c: "c",
  cond: boolean,
): void {
  switch (y) {
    case "a":
      // @skjs-expect-error Fallthrough case in switch; add a 'break'
      if (cond) {
        y = c;
        break;
      }
    case "b":
      // Pins today's behaviour: the kept break branch widens `y` to include
      // "c" here. The next commit drops the branch; the write still reaches
      // the code after the switch (see the function below), but not this
      // clause.
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const z: "a" | "b" = y;
      break;
    default:
      break;
  }
}

// The dropped branch's write is not lost: the jump edge carries it, so the
// state after the switch still includes it.
function breakSubpathWriteReachesAfterTheSwitch(
  y: "a" | "b" | "c",
  c: "c",
  cond: boolean,
): void {
  switch (y) {
    case "a":
      if (cond) {
        y = c;
        break;
      }
      break;
    default:
      break;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const z: "a" | "b" = y;
}
