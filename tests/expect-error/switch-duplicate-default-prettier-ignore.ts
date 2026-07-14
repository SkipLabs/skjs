// Two `default` clauses in one switch is a JavaScript SyntaxError (tsc reports
// TS1113); prettier itself refuses to parse it, hence the `-prettier-ignore`
// filename. SKJS must reject the second `default`.
//
// FIXME: SKJS currently accepts this silently. Pinned to the current (incorrect)
// behavior — no diagnostic; the second `default` is rejected in the next commit.
function duplicateDefault(x: number): void {
  switch (x) {
    case 1:
      return;
    default:
      return;
    case 2:
      return;
    default:
      return;
  }
}
