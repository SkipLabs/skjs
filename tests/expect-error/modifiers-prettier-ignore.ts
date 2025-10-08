// @ts-expect-error Forbidden modifier for a function parameter
function forbiddenModifiers(public x: string): void {}

// @ts-expect-error 'public' modifier cannot appear on a type member.
function forbiddenModifiersOnObjectType(x : { public f: string}): void {}
