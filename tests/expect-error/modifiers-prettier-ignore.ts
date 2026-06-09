// @ts-expect-error Forbidden modifier 'public' for a function parameter
function forbiddenModifiers(public x: string): void {}

// @skjs-expect-error Member 'public' must have an explicit type annotation
function forbiddenModifiersOnObjectType(x : { public f: string}): void {}
