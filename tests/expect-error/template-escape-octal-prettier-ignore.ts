// prettier-ignore
// Octal escapes are always invalid in template literals (tsc TS1487); leaving
// them undecoded is unsound (#810), so skjs rejects them.
class TemplateOctal {
  // @skjs-expect-error Octal escape sequences are not allowed
  a: string = `\1`; }
