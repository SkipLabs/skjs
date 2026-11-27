// Side-effect import of an existing stub package introduces no local bindings.
// prettier-ignore
import 'for-tests';
import "for-tests";

function ok(): number {
  return 1;
}

function noBindingsIntroduced(): void {
  // @ts-expect-error Cannot find name
  functionFromStubs("blah");
}
