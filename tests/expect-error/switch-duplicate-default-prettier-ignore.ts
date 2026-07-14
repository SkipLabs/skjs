// Two `default` clauses in one switch is a JavaScript SyntaxError (tsc reports
// TS1113); prettier itself refuses to parse it, hence the `-prettier-ignore`
// filename. SKJS rejects the second `default`.
function duplicateDefault(x: number): void {
  switch (x) {
    case 1:
      return;
    default:
      return;
    case 2:
      return;
    // @skjs-expect-error A 'default' clause cannot appear more than once in a 'switch' statement
    default:
      return;
  }
}
