// A modifier keyword before `(` in an interface (e.g. `public(x: string): number`)
// must NOT silently turn into a callable signature on the interface.
// (Matches the existing `class-method-named-*-prettier-ignore.ts` parse error
// when modifiers() consumes the keyword; a future parser fix can allow
// modifier-named methods across both classes and interfaces uniformly.)
interface ModMethodName {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  public(x: string): number; }
