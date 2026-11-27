// Side-effect imports of relative and bare modules succeed and introduce no local bindings.
import "./side-effect.js";
// prettier-ignore
import './side-effect.js';
import "for-tests";

function noBindingLeaked(): boolean {
  // @ts-expect-error Cannot find name
  return sideEffectLoaded;
}
