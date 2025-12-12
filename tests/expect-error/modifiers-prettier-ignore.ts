// @ts-expect-error Forbidden modifier for a function parameter
function forbiddenModifiers(public x: string): void {}

// @ts-expect-error Type annotation expected
function forbiddenModifiersOnObjectType(x : { public f: string}): void {}
