// prettier-ignore
// Octal escapes are always invalid in template literals (tsc TS1487); leaving
// them undecoded is unsound (#810), so skjs rejects them. Pinned to the pre-fix
// behavior, which accepted the raw lexeme.
function templateOctal(): void {
  const a: string = `\1`;
}
