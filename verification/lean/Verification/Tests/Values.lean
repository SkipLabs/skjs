import Verification.Calculus.Values

/-!
Pins `Calculus/Values.lean`: the value domain, and `===` on it.

**These definitions are in the trusted base.** No theorem constrains them:
they say what a runtime value *is*, so a mistake here changes what soundness
means rather than breaking a proof. Executable checks are the only evidence.

What belongs here: cases that fix value identity, especially where the model
and JavaScript are known to differ. `===` is the derived `DecidableEq Val`
instance, so it compares numbers by bit pattern.

Not yet covered: strings beyond ASCII (Lean strings are Unicode scalars,
JavaScript strings are UTF-16 code units), and the full NaN range.
-/

namespace Verification
namespace Tests

open Core

-- `-0` and `+0` are distinct bit patterns, hence distinct values here. The
-- decoder normalises one to the other (`numBits`); the value domain does not.
#guard (Val.vnum ((0.0 : Float).toBits) == Val.vnum ((-0.0 : Float).toBits)) == false

-- Same bit pattern, same value: `===` is bit equality. For a NaN pattern this
-- differs from JavaScript, where `NaN === NaN` is false.
#guard Val.vnum ((0.0 / 0.0 : Float).toBits) == Val.vnum ((0.0 / 0.0 : Float).toBits)

-- Values of different tags are never equal.
#guard (Val.vnull == Val.vundef) == false
#guard (Val.vbool false == Val.vnum ((0.0 : Float).toBits)) == false
#guard (Val.vstr "" == Val.vnum ((0.0 : Float).toBits)) == false

end Tests
end Verification
