/-! The runtime values shared by the type and program languages. -/

namespace Verification
namespace Core

/-- A value, abstracted to what types can observe.

A number is identified by the bit pattern of its IEEE-754 double, with `-0`
normalised to `+0`, so `-0` and `0` are one value and two spellings of one
double are indistinguishable. -/
inductive Val where
  | vnull
  | vundef
  | vnum (bits : UInt64)
  | vstr (s : String)
  | vbool (b : Bool)
  deriving DecidableEq, Repr

end Core
end Verification
