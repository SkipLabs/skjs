// Two `default` clauses in one switch is a JavaScript SyntaxError (tsc reports
// TS1113); prettier itself refuses to parse it, hence the `-prettier-ignore`
// filename. SKJS rejects the second `default`. The first one is not last
// either, so it also draws the `default-case-last` warning.
function duplicateDefault(x: number): void {
  switch (x) {
    case 1:
      return;
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
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

// The two `default` positions a switch tracks are distinct, and both are
// observable here: the duplicate is reported at the *second* `default`, naming
// the *first* as the one it conflicts with, while `default-case-last` fires on
// the first (the only one that is not last). With a literal scrutinee the cases
// also cover the whole type, so the *last* `default` is the one reported
// unreachable.
function duplicateDefaultOverLiteral(x: 1): void {
  switch (x) {
    case 1:
      return;
    // @skjs-expect-warning The 'default' clause should be the last branch of a switch
    default:
      return;
    // @skjs-expect-error A 'default' clause cannot appear more than once in a 'switch' statement
    // @skjs-expect-error-line2 First 'default' clause was here
    // @skjs-expect-warning This 'default' case is unreachable: all values of the switched type are already handled
    default:
      return;
  }
}
