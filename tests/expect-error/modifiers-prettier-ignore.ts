// @ts-expect-error Forbidden modifier for a function parameter
function forbiddenModifiers(public x: string): void {}

// TODO: should be forbidden
function forbiddenModifiersOnObjectType(x : { public f: string}): void {}
