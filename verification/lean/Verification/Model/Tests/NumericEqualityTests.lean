import Verification.Model.Source.RequestJson

namespace Verification.Model.NumericEqualityTests

-- IEEE encodings: every NaN compares unequal, infinities compare by sign, and
-- distinct finite doubles stay distinct.
#guard !(numberEqual 0x7ff8000000000000 0x7ff8000000000000)
#guard !(numberEqual 0x7ff0000000000001 0)
#guard !(numberEqual 0 0xfff8000000000000)
#guard numberEqual 0x7ff0000000000000 0x7ff0000000000000
#guard !(numberEqual 0x7ff0000000000000 0xfff0000000000000)
#guard !(numberEqual 0x3ff0000000000000 0x3ff0000000000001)

end Verification.Model.NumericEqualityTests
