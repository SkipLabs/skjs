// A type predicate (`x is T`) is verified on implemented functions and methods
// (see `type-predicate-bodied.ts`): valid bodies whose return expressions
// soundly prove both true and false directions are accepted, while lying or
// incomplete bodies are rejected.

function isString(x: unknown): x is string {
  return typeof x === "string";
}

function badIsString(x: unknown): x is string {
  // @skjs-expect-error Cannot prove 'x' is 'string' when returning 'true': 'x' has type 'number'
  return typeof x === "number";
}

class Checker {
  isNumber(x: unknown): x is number {
    return typeof x === "number";
  }

  badIsNumber(x: unknown): x is number {
    // @skjs-expect-error Cannot prove 'x' is 'number' when returning 'true': 'x' has type 'string'
    return typeof x === "string";
  }
}
