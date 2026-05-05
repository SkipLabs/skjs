// @ts-expect-error Forbidden modifier 'public' for a function parameter
function forbiddenModifiers(public x: string): void {}

// @ts-expect-error Type annotation expected for 'public'
function forbiddenModifiersOnObjectType(x : { public f: string}): void {}
