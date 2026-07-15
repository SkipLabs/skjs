// Two `default` clauses in one switch is a JavaScript SyntaxError (tsc reports
// TS1113); prettier itself refuses to parse it, hence the `-prettier-ignore`
// filename. SKJS rejects the second `default`. The first one is not last
// either, so it also draws the `default-case-last` warning.
function duplicateDefault(x: number): void {
  // @skjs-expect-warning The 'default' clause should be the last branch of a switch
  switch (x) {
    case 1:
      return;
    default:
      return;
    case 2:
      return;
    // @skjs-expect-error A 'default' clause cannot appear more than once in a 'switch' statement
    // @skjs-expect-error-line2 First 'default' clause was here
    default:
      return;
  }
}
