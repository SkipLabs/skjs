import Verification.Model.Programs.CertificateProducer

namespace Verification.Model.ConstructTests

-- A plain call dispatches nothing on construct-only code.
#guard CallArguments.dispatch (.graph 1 [.var 1] [(.ret, none)] 0 [] .construct) .undef [] = none
-- `new` runs no call-only code.
#guard (CallArguments.construction (.graph 1 [.var 1] [(.ret, none)] 0 [])).isNone

end Verification.Model.ConstructTests
