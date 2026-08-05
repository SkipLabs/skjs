// Lambdas get their own CGNode and CFG, so they are annotated like any other
// function. One that starts its own line is annotated above it; one passed
// inline as an argument gets a single-line block comment in front of it,
// which is the only form that fits mid-expression.
//
// The lambdas live inside a function because a top-level constant may not have
// an object type.

function apply(f: (n: number) => number, x: number): number {
  return f(x);
}

function useLambdas(): number {
  const triple = (n: number): number => n * 3;
  const nine = triple(3);

  // Inline argument: annotated in front of the lambda, not above the line.
  const doubled = apply((n: number): number => n * 2, 21);

  const branching = (n: number): number => {
    if (n < 0) {
      return 0;
    }
    return n;
  };

  return nine + doubled + branching(7);
}

const _ = useLambdas();
