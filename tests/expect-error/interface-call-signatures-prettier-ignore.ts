// prettier-ignore
interface Callable {
  // @skjs-expect-error 'a variable name' or 'a number' or '-' or ''' or '"' expected
  (x: string): number; }
