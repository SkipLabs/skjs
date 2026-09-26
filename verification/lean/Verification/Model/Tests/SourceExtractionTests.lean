import Verification.Model.Source.SourceExtraction

namespace Verification.Model.SourceExtractionTests
open Lean PositiveNormalization ProgramTyping RequestJson SourceExtraction

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

private def is [BEq α] (r : Except String α) (expected : α) : Bool :=
  match r with | .ok a => a == expected | .error _ => false

-- Exercise the source-specific vocabulary, not every unrelated signature in
-- the whole type table. The independent checker still receives the full graph.
private def produceSourceJson (j : Json) (fuel : Nat)
    (suggestions : List (ProgramCertificates.Sequent Nat) := [])
    (known : List (ProgramCertificates.Evidence Nat) := []) : Except String Json := do
  let r ← decodeRequest j
  let source : SourceRequest := ⟨r,[],[],[],[],[], [], []⟩
  RequestJson.produceJson j fuel suggestions known [] (some source.searchLabels)

-- Runtime numeric operations retain signed zero. This is the same expression
-- executed by the JS arithmetic suite: merging its zeros changes false to true.
private def signedZeroComparison : Bool :=
  let zero := (0.0 : Float).toBits
  let one := (1.0 : Float).toBits
  let z := arithBits .mul zero (arithBits .sub zero one)
  numberEqual (arithBits .div one (arithBits .add (arithBits .div one z)
    (arithBits .div one zero))) zero
#guard !signedZeroComparison
#guard is (literalBits "-0") (9223372036854775808 : UInt64)
#guard is (literalBits "-0.0") (9223372036854775808 : UInt64)
#guard numberEqual (9223372036854775808 : UInt64) 0

-- The binary operators on values, against what node computes for the same
-- operands: `ToInt32` through `^` (and so `~`), JavaScript's corrections to
-- `pow`, exact comparison across number and bigint, UTF-16 string order, and
-- the combinations that throw, which have no value.
private def dbl (f : Float) : Tm := .num f.toBits
private def isNaNValue : Option Tm → Bool
  | some (.num b) => (Float.ofBits b).isNaN
  | _ => false
#guard binop .xor (dbl 4294967296.5) (dbl (-1.0)) == some (dbl (-1.0))
#guard binop .xor (dbl (-3000000000.7)) (dbl (-1.0)) == some (dbl (-1294967297.0))
#guard isNaNValue (binop .pow (dbl 1.0) (dbl (0.0 / 0.0)))
#guard isNaNValue (binop .pow (dbl (-1.0)) (dbl (1.0 / 0.0)))
#guard binop .lt (dbl 9007199254740993.0) (.bigint 9007199254740993) == some .tru
#guard binop .le (dbl (0.0 / 0.0)) (.bigint 2) == some .fls
#guard binop .gt (.bigint (-1)) (dbl (-0.5)) == some .fls
#guard binop .lt (.str (String.singleton (Char.ofNat 0x10000))) (.str (String.singleton (Char.ofNat 0xFFFF))) == some .tru
#guard binop .div (.bigint 7) (.bigint (-2)) == some (.bigint (-3))
#guard binop .xor (.bigint 5) (.bigint (-1)) == some (.bigint (-6))
#guard binop .div (.bigint 7) (.bigint 0) == none
#guard binop .pow (.bigint 2) (.bigint (-1)) == none
#guard binop .add (.bigint 1) (dbl 1.0) == none
#guard binop .lt (.str "1") (dbl 2.0) == none
-- `%` on doubles is the exact remainder with the dividend's sign, and on
-- bigints the truncating one; a zero bigint divisor throws. Bits from node.
#guard binop .rem (dbl 5.5) (dbl 2.0) == some (dbl 1.5)
#guard binop .rem (dbl (-5.0)) (dbl 3.0) == some (dbl (-2.0))
#guard binop .rem (dbl 5.0) (dbl (-3.0)) == some (dbl 2.0)
#guard binop .rem (dbl (-4.0)) (dbl 2.0) == some (.num 9223372036854775808)
#guard binop .rem (dbl 7.0) (dbl (1.0 / 0.0)) == some (dbl 7.0)
#guard isNaNValue (binop .rem (dbl (1.0 / 0.0)) (dbl 2.0))
#guard isNaNValue (binop .rem (dbl 2.0) (dbl 0.0))
#guard remBits 9094988921128908188 4613937818241073152 == 0
#guard remBits 1 4611686018427387904 == 1
#guard remBits 3 2 == 1
#guard remBits 9214871658872686752 2024022533073106 == 708093261633040
#guard remBits 4599075939470750515 4591870180066957722 == 4591870180066957720
#guard remBits 13843220829606772736 4602678819172646912 == 13821547256400052224
#guard remBits 4845873199050653696 118622047889322841 == 117815928586361606
#guard binop .rem (.bigint (-7)) (.bigint 2) == some (.bigint (-1))
#guard binop .rem (.bigint 7) (.bigint (-2)) == some (.bigint 1)
#guard binop .rem (.bigint 7) (.bigint 0) == none
#guard binopThrows .rem (.bigint 7) (.bigint 0)
#guard binop .rem (.bigint 7) (dbl 2.0) == none

-- `Number::toString` against node's `String(x)` for the same bits: the
-- shortest round-tripping digits, the closest of them, the three notations,
-- both zeros, the halved gap below a power of two, subnormals, and 300 more
-- pseudo-random doubles and short decimals.
#guard numberToString 0x3fb999999999999a == "0.1"
#guard numberToString 0x3fd3333333333334 == "0.30000000000000004"
#guard numberToString 0x444b1ae4d6e2ef50 == "1e+21"
#guard numberToString 0x441ac53a7e04bcda == "123456789012345680000"
#guard numberToString 0x0000000000000001 == "5e-324"
#guard numberToString 0x0000000000000003 == "1.5e-323"
#guard numberToString 0x7fefffffffffffff == "1.7976931348623157e+308"
#guard numberToString 0x0010000000000000 == "2.2250738585072014e-308"
#guard numberToString 0x7fe0000000000000 == "8.98846567431158e+307"
#guard numberToString 0x3eb0c6f7a0b5ed8d == "0.000001"
#guard numberToString 0x3eb421f5f40d8376 == "0.0000012"
#guard numberToString 0x3e7ad7f29abcaf48 == "1e-7"
#guard numberToString 0x4340000000000000 == "9007199254740992"
#guard numberToString 0x4341c37937e08000 == "10000000000000000"
#guard numberToString 0x8000000000000000 == "0"
#guard numberToString 0x7ff8000000000000 == "NaN"
#guard numberToString 0xfff0000000000000 == "-Infinity"
#guard numberToString 0x4059000000000000 == "100"
#guard numberToString 0x3c36b082c2148b8e == "1.23e-18"
#guard numberToString 0xbdf12e0be826d695 == "-2.5e-10"
#guard numberToString 0x44b52d02c7e14af6 == "1e+23"
#guard numberToString 0x4011666666666666 == "4.35"
private def numberStrings : List (UInt64 × String) := [
  (0x1628380898e8f8c8, "6.179694342732706e-202"),
  (0xf3a74b1f63573bea, "-1.3029273641170615e+249"),
  (0xd235f8c858a85387, "-1.092709018800459e+88"),
  (0xabffc3379b2f33e7, "-9.293878748722865e-97"),
  (0x8bfad85e6c2cecac, "-5.858549713169948e-251"),
  (0x6cc7eb3f0377db6f, "1.0306914204838005e+216"),
  (0x73c2cacd79b541dd, "4.2045933389570795e+249"),
  (0x494591ed19fde900, "9.620552241985708e+44"),
  (0x30c858a8b82317fb, "1.076525883721656e-73"),
  (0x0f93c7eb670bdf23, "1.2442573212271916e-233"),
  (0x17fb0f9362ead29a, "3.7070129997144725e-193"),
  (0xead29ac2ca327a22, "-3.733153579968913e+206"),
  (0xaa92f5811d8985d1, "-1.322625704653163e-103"),
  (0xc85843ed504070e0, "-3.3028269135495556e+40"),
  (0x2b7f43b743b71baf, "3.573494660476618e-99"),
  (0xb4d47494347cfc7c, "-3.336940611547511e-54"),
  (0xfc7cfc7cfc7cfc17, "-4.5196867435304834e+291"),
  (0xfbaa925a828af23a, "-5.057607376436528e+287"),
  (0xe26aed19d5e1fde9, "-1.2404586726182648e+166"),
  (0x65310db99080b048, "2.764227795553952e+179"),
  (0xd828d33dfb0f93c7, "-4.890806427381093e+116"),
  (0xeb3f9e766e065915, "-4.0605519687631974e+208"),
  (0x20d05beff414b4d4, "1.2494025391805135e-150"),
  (0x74943454f414b4d4, "3.703247871720631e+253"),
  (0x742f3382c0f06010, "4.467842834055035e+251"),
  (0x0030a0504070e090, "9.248644399688898e-308"),
  (0x80b020d0c0f0fb0f, "-2.296729827789709e-305"),
  (0x93c85843b71b4ab2, "-2.2598467834627802e-213"),
  (0xfaa22a12da020a72, "-5.275526525051736e+282"),
  (0xba62ead29a5dc9c5, "-1.9101567368294615e-27"),
  (0x3975019d090551ad, "6.473066695494187e-32"),
  (0x74ca04e444248464, "3.8152127279768084e+254"),
  (0xc4a4047f43b71b4a, "-4.726514350414092e+22"),
  (0xe8ca327a22aa2d59, "-6.119580696629709e+196"),
  (0x1521d85e6c2cecac, "6.947909975910976e-207"),
  (0x6cc7eb3f0377db0a, "1.030691420483785e+216"),
  (0x72ba62ea6e06be16, "4.5041875656333696e+244"),
  (0x29dcdcdcdcdcdcdc, "4.915856379993723e-107"),
  (0xdcdcdcdcdcdcdcdc, "-2.1482046286569577e+139"),
  (0x7712da020a9a9080, "3.7991309464576e+265"),
  (0xb020d0c0f0601000, "-7.261050442106517e-77"),
  (0x303b4fd3072b7f43, "2.3586942736542673e-76"),
  (0x521add80b020d05b, "3.3401776318026033e+87"),
  (0xeff3a8b888186813, "-1.9075659513849588e+231"),
  (0x4706811d8985d12d, "1.4606162738071434e+34"),
  (0xf44ab2faa2c5116d, "-1.5292680327191584e+252"),
  (0x348ac4a4047f43b7, "1.3646108073630292e-55"),
  (0xb6ae46fe7ed6e965, "-2.6517226956627185e-45"),
  (0x310d54f4afb38f13, "2.0751554564252843e-72"),
  (0x476bbf839290804b, "1.1526110373082383e+36"),
  (0x1f6357d684362ec6, "1.7610785824421388e-157"),
  (0x7ed64e019d090551, "9.559876406450392e+302"),
  (0xadd9953cbc3cbc3c, "-8.037704443317413e-88"),
  (0xbc3c573b4fd3072b, "-1.5363550696649428e-18"),
  (0x7f43b71bafb3670b, "1.0816039647674107e+305"),
  (0xdf2317960e265e36, "-1.953000318585863e+150"),
  (0xc9c51108cee6b9b8, "-2.4053737231763487e+47"),
  (0x88186813476b5a82, "-1.1549686176691463e-269"),
  (0x25f1cd79b541dd49, "6.574855175400578e-126"),
  (0x4591edb4d47494cf, "1.38715363282219e+27"),
  (0x5387abffc3379bca, "2.468887225458792e+94"),
  (0x3215e444241f6357, "2.030017438555013e-67"),
  (0x3b4fd32f330f93ef, "5.2649945001083196e-23"),
  (0xf3a7e6542a12da02, "-1.3368395210231605e+249"),
  (0x0a7255617d69e5b1, "2.384786792825654e-258"),
  (0x8d39759c9c9c9cc4, "-5.826021193109838e-245"),
  (0xa404e4df5a828af2, "-3.593306260102976e-135"),
  (0x3ae2055148d828d3, "4.6582602664160825e-25"),
  (0x072b7f43521a424a, "3.9710118520156496e-274"),
  (0xb2faa2521a424ab2, "-4.0464891402697616e-63"),
  (0x95d78d3975019da4, "-1.8779517316748453e-203"),
  (0x04e444248464c4a4, "4.258984483494202e-285"),
  (0x04e444bf83f75bef, "4.2594815118941134e-285"),
  (0x1bafb4d47494cf53, "2.5037964322616235e-175"),
  (0x87ac6c2cecd4742f, "-1.0507928856059504e-271"),
  (0x33e78b5fa3977b8f, "1.1721386854908854e-58"),
  (0x134706be168ea6de, "8.349452400571688e-216"),
  (0xb6ae46fe566a521a, "-2.651722484638634e-45"),
  (0x424a4df935c15dc9, "225954655106.7327"),
  (0xc5ac6c2cecac072b, "-4.3981782067344067e+27"),
  (0x7f43521a42e5b18d, "1.0599582980001961e+305"),
  (0xd474943454f414b4, "-7.03301021653092e+98"),
  (0xd47494cf5322aa92, "-7.033818475372492e+98"),
  (0x5a828af23ae20587, "1.0041590804146269e+128"),
  (0x7d69e5b18d397501, "1.3231809649233826e+296"),
  (0x9d0905ecac6cc7ae, "-8.288086825191507e-169"),
  (0x46fe56cee61ef6ee, "9.845599075151434e+33"),
  (0x863e960e26867327, "-1.3479968782204266e-278"),
  (0xcb3ae20588186878, "-2.574869977111736e+54"),
  (0xe3d7bb6a521a6a52, "-9.171355646043728e+172"),
  (0x1a424ab2fa3d29a5, "3.443887224645441e-182"),
  (0x714df935c15dc960, "6.099352229245845e+237"),
  (0x100030a0eb3f9e76, "1.3035238935735798e-231"),
  (0x0905ecac9434548f, "3.399724240554644e-265"),
  (0x134706be1629a571, "8.34945239204425e-216"),
  (0x75019d0905ece2a0, "4.132282470214731e+255"),
  (0x50db6f7327cb9fe3, "3.253039716014637e+81"),
  (0xd756ce81e0f9355c, "-5.48479324225994e+112"),
  (0x5cd2977b2a12da02, "1.383750071536529e+139"),
  (0x0a72ba6285d1c858, "2.436108664365534e-258"),
  (0x43b71baf4e29a571, "1665117237484548400"),
  (0x4d943454f414b4d4, "5.319434768831448e+65"),
  (0x7494cf538746fe56, "3.814219638971421e+253"),
  (0xcee61ef6ee86d995, "-1.2213857838189922e+72"),
  (0xa1bd442484fff907, "-3.6620830456809486e-146"),
  (0x2b7f43b71baf4e9c, "3.573494387759584e-99"),
  (0x9c9c9c9c379b2f33, "-7.4036695245080985e-171"),
  (0xe7b3670bdf2317fb, "-3.4579245184792075e+191"),
  (0x0f2efc7c977b8f13, "1.5227296012705697e-235"),
  (0x476be7587a224591, "1.1590740934063066e+36"),
  (0xed19d5e1fde90066, "-3.562488039723797e+217"),
  (0xd4742f33828a1a10, "-6.898171748679926e+98"),
  (0x0030a0504070e090, "9.248644399688898e-308"),
  (0x80b020d0c08b5fa3, "-2.2967298244208047e-305"),
  (0x97168ea6de51add9, "-1.8860304158728027e-197"),
  (0x95a1bda925f1cd79, "-1.768266326166399e-204"),
  (0xb541dde444241f63, "-3.7307544645173945e-52"),
  (0xf23ae26aed19d57c, "-1.7926586103841217e+242"),
  (0xfc7cfc7cfc7c97b1, "-4.5196867435162456e+291"),
  (0x5fa3327a22aa925a, "5.027188485601421e+152"),
  (0x828a8d3975019d09, "-2.029952729014077e-296"),
  (0x0551ad74ca687848, "4.755174802172033e-283"),
  (0x0030c858a8b888b3, "9.335632708676031e-308"),
  (0x670bdf2317fb0f93, "2.42543512935825e+188"),
  (0xc7eb3f9e766ea1bd, "-2.8975587673727886e+38"),
  (0xa9c0f060100030a0, "-1.4425087219378537e-107"),
  (0x504070e09080b020, "3.807458475803581e+78"),
  (0x6bbf83f7f60030a0, "1.0360989080046842e+211"),
  (0x7848d828380833e7, "2.6250282935352852e+271"),
  (0x8b5fa397168ea6de, "-6.7429004595015646e-254"),
  (0xb6aee133b9f5811d, "-2.7044793705110766e-45"),
  (0x248464c41a42e5b1, "8.978549592922839e-133"),
  (0x286e06be168ea679, "6.096407957457762e-114"),
  (0xb541dd49452cec47, "-3.7302606188988235e-52"),
  (0xa18f13476bbf83f7, "-4.8605742123569063e-147"),
  (0x5beff3a74b1f6357, "7.2574327488690825e+134"),
  (0x3b4f6e3cf23ae26a, "5.199759481586234e-23"),
  (0x52b541dd49459188, "2.70636561515721e+90"),
  (0x180377db6f7327cb, "5.333820672793271e-193"),
  (0x9fe3d7bbcf5322aa, "-4.624802765288228e-155"),
  (0x2d5915bc3cbc3cbc, "3.07860339899206e-90"),
  (0x3cbc3cbcd7bbcfee, "3.91870654135468e-16"),
  (0xbc3c573b4fd3072b, "-1.5363550696649428e-18"),
  (0xa74b1f63573b4f6e, "-2.1006959705715737e-119"),
  (0x3c8ea679b5417848, "5.316978561799415e-17"),
  (0x0030a0504098e8f8, "9.248644404873804e-308"),
  (0xc858a8b888b3670b, "-3.3564181058551187e+40"),
  (0xdf23b2faa22a1275, "-2.015092799720309e+150"),
  (0x380898e893c7eb3f, "9.03562057522345e-39"),
  (0x03ed1970e0b88818, "9.33120863099556e-290"),
  (0x6878487327cb9fe3, "1.7726364489662754e+195"),
  (0xd7bb6a521a424ab2, "-4.219603213943401e+114"),
  (0xfaa22aadd930a050, "-5.276213417528953e+282"),
  (0x4070e02bb6ae46fe, "270.01067226483417"),
  (0x56cee6b92b51add9, "1.4514586383667973e+110"),
  (0x30a0eb027327cb3a, "1.8701664328537268e-74"),
  (0xe26aed1970a397a3, "-1.2404583946111269e+166"),
  (0x977b2a127501383e, "-1.4535904157398551e-195"),
  (0x960e265e362ec67e, "-1.9232619675617881e-202"),
  (0xfe56cee6b92bb577, "-3.8186236326874704e+300"),
  (0xadd9953cbcd7bc3c, "-8.037704454655848e-88"),
  (0xbc3cbc3c5772ba62, "-1.5577435033976445e-18"),
  (0xead29ac265687848, "-3.733152374514825e+206"),
  (0xd8c4a404e4442484, "-4.164019072757292e+119"),
  (0x64c4a404e444bf83, "2.613797134796655e+177"),
  (0x925a828af2d5e1fd, "-2.933538603499359e-220"),
  (0xe965cc0c4c8ccca7, "-5.213929029620001e+199"),
  (0x4b1f6357d68464c4, "7.515946958107808e+53"),
  (0xa4047f435250400b, "-3.525046256822121e-135"),
  (0xdf2317960ec19434, "-1.953000322282529e+150"),
  (0x54f41450400bdf23, "1.7567428716829562e+101"),
  (0x17fb0f0905ecac07, "3.706723782841729e-193"),
  (0x2b7f43b71bafb367, "3.573494387770062e-99"),
  (0x0bdf2317fb379b2f, "1.6987973752252353e-251"),
  (0x33e78b5fa3977b8f, "1.1721386854908854e-58"),
  (0x13476bbf83f75bef, "8.492519081085196e-216"),
  (0x8edcdc7848d82860, "-4.432185884352265e-237"),
  (0x100030a0eb3f0377, "1.30352389356223e-231"),
  (0xdb6f7327f3a7e61e, "-2.7903995518444328e+132"),
  (0xf6ee863e960ec15c, "-7.689413842299388e+264"),
  (0x5c5c5cf75beff3a7, "8.246174130990142e+136"),
  (0x4b20d0c0f0601000, "8.052997803324513e+53"),
  (0x30a0504070e09080, "1.803340690144307e-74"),
  (0xb020d0c0f0601000, "-7.261050442106517e-77"),
  (0x588f13476bbf8392, "3.91817439966914e+118"),
  (0x5a828af23ae26a52, "1.0041590804195912e+128"),
  (0x1a424ab2faca327a, "3.443887230827856e-182"),
  (0x224591ed1970168e, "1.3819193795757892e-143"),
  (0xa6deb6ae46fe56ce, "-1.8584566639370464e-121"),
  (0x811d8920069080b0, "-2.6918498882050383e-303"),
  (0xbbcf538746100030, "-1.3267196849803982e-20"),
  (0xa05040707b8f1347, "-4.84843351992385e-153"),
  (0x6bbf1e2c227cfc7c, "1.0230261095149298e+211"),
  (0xfc7cfc17fb0f2ec6, "-4.5194464283179517e+291"),
  (0x19d5e1fde965cc0c, "3.2187346042783814e-184"),
  (0x4c27cb9fe3d7bbcf, "7.468309992557081e+58"),
  (0x53afb3670b7a587a, "1.3225093514729997e+95"),
  (0x224591ed1970168e, "1.3819193795757892e-143"),
  (0xa6deb6d64e669e76, "-1.8584936225670812e-121"),
  (0x6e06beb18d397501, "1.0277104933754685e+222"),
  (0x3f23f702d649225e, "0.00015232"),
  (0x3f314272964a84b4, "0.00026336"),
  (0x3f4b02e5b8811061, "0.00082432"),
  (0x40d3100000000000, "19520"),
  (0x40f80e0000000000, "98528"),
  (0x3f46c91a3abec2c9, "0.00069536"),
  (0x40f2f00000000000, "77568"),
  (0x3f3a876ac2ec793a, "0.0004048"),
  (0x3ffc779a6b50b0f2, "1.7792"),
  (0x3f432daf3ac09b3b, "0.00058528"),
  (0x400caa64c2f837b5, "3.5832"),
  (0x40dec00000000000, "31488"),
  (0x4012b020c49ba5e3, "4.672"),
  (0x40088ce703afb7e9, "3.0688"),
  (0x40de100000000000, "30784"),
  (0x402217c1bda5119d, "9.0464"),
  (0x40da600000000000, "27008"),
  (0x401cbc6a7ef9db23, "7.184"),
  (0x401ade00d1b71759, "6.7168"),
  (0x40f6f20000000000, "93984"),
  (0x3f4ae2af622dc78e, "0.00082048"),
  (0x40c4700000000000, "10464"),
  (0x3f4401bf9dba3aa4, "0.00061056"),
  (0x3fe70a3d70a3d70a, "0.72"),
  (0x3f394aa9c7642d26, "0.00038592"),
  (0x40f1680000000000, "71296"),
  (0x4022bb98c7e28241, "9.3664"),
  (0x401dcc63f141205c, "7.4496"),
  (0x3f49db9e4bdaf4d9, "0.00078912"),
  (0x4001604189374bc7, "2.172"),
  (0x40d7f00000000000, "24512"),
  (0x40f1320000000000, "70432"),
  (0x40f7cb9000000000, "97465"),
  (0x400cfaacd9e83e42, "3.6224"),
  (0x4011a5e353f7ced9, "4.412"),
  (0x3f4665c805e8a240, "0.00068352"),
  (0x400161e4f765fd8b, "2.1728"),
  (0x40f7f00000000000, "98048"),
  (0x3fd8c7e28240b780, "0.3872"),
  (0x40f5f60000000000, "89952"),
  (0x40eef80000000000, "63424"),
  (0x3f4749f3940be612, "0.00071072"),
  (0x40f3e60000000000, "81504"),
  (0x3f4e405ce761a389, "0.0009232"),
  (0x3f1edebd6525c993, "0.00011776"),
  (0x3f40b42d43b00313, "0.00050976"),
  (0x40225fd8adab9f56, "9.1872"),
  (0x3f366069a230161d, "0.00034144"),
  (0x3f3bef1edc392667, "0.00042624"),
  (0x3f37cd7c1f354f6d, "0.0003632"),
  (0x40d9280000000000, "25760"),
  (0x40d3d80000000000, "20320"),
  (0x3f1a5719416f8bff, "0.00010048"),
  (0x3f20461e4768ca44, "0.00012416"),
  (0x3f48bc6474c9ab85, "0.00075488"),
  (0x40ea7c0000000000, "54240"),
  (0x3f400860cc9e7eb1, "0.00048928"),
  (0x3f49bb67f587ac06, "0.00078528"),
  (0x40e2140000000000, "37024"),
  (0x40d1880000000000, "17952"),
  (0x400a8c154c985f07, "3.3184"),
  (0x40f14a0000000000, "70816"),
  (0x4021d7dbf487fcb9, "8.9216"),
  (0x40213c36113404ea, "8.6176"),
  (0x3f2e88d7299d0762, "0.00023296"),
  (0x3f322d54211477b1, "0.00027736"),
  (0x401bbcd35a858794, "6.9344"),
  (0x40f25a0000000000, "75168"),
  (0x40f0fe0000000000, "69600"),
  (0x401645a1cac08312, "5.568"),
  (0x40202c3c9eecbfb1, "8.0864"),
  (0x40f56c0000000000, "87744"),
  (0x3f3539223589fa95, "0.00032384"),
  (0x40f2660000000000, "75360"),
  (0x40eb200000000000, "55552"),
  (0x3ff7cb923a29c77a, "1.4872"),
  (0x4022b020c49ba5e3, "9.344"),
  (0x3f501dda5b80af3d, "0.00098368"),
  (0x40169e1b089a0275, "5.6544"),
  (0x3f41f64ca2f0db4a, "0.00054816"),
  (0x401a474538ef34d7, "6.5696"),
  (0x40f1560000000000, "71008"),
  (0x3f4721afa823cb0b, "0.00070592"),
  (0x3f48cf2ed1cf9600, "0.00075712"),
  (0x40f80e0000000000, "98528"),
  (0x40f4b40000000000, "84800"),
  (0x3f42e285c6a8f150, "0.00057632"),
  (0x4014e075f6fd21ff, "5.2192"),
  (0x3f4d394bd10ed0d3, "0.00089184"),
  (0x40ee640000000000, "62240"),
  (0x40e9e80000000000, "53056"),
  (0x3f4db4c6c6a367fa, "0.00090656"),
  (0x3f21f39d71149538, "0.00013696"),
  (0x3ff15b573eab367a, "1.0848"),
  (0x3f4038b24e1b6bec, "0.00049504"),
  (0x3f46fc1aee17f616, "0.00070144"),
  (0x3f4d19157abb8801, "0.000888"),
  (0x3f3d26817408e659, "0.0004448"),
  (0x3f405e47082740e2, "0.00049952"),
  (0x3f499324099f90ff, "0.00078048")]
#guard numberStrings.all fun (b, s) => numberToString b == s
-- `+` with a string operand concatenates, converting a primitive other than
-- a symbol by `ToString`; a symbol or an object has no answer.
#guard binop .add (.str "a") (.str "b") == some (.str "ab")
#guard binop .add (.str "n=") (dbl 1.5) == some (.str "n=1.5")
#guard binop .add (.bigint (-12)) (.str "n") == some (.str "-12n")
#guard binop .add (.str "") .tru == some (.str "true")
#guard binop .add .nul (.str "") == some (.str "null")
#guard binop .add (.str "") .undef == some (.str "undefined")
#guard binop .add (.str "") (.sym 0) == none
#guard binop .sub (.str "1") (.str "1") == none
#guard binop .add .tru (dbl 1.0) == none

-- Exact finite-set translation, including normalization of unions.
#guard is (SourceTypes.translate ⟨false,[.bool]⟩) ([1,2])
#guard is (SourceTypes.translate ⟨false,[.boolLit true]⟩) ([1])
#guard is (SourceTypes.translate ⟨false,[.boolLit false]⟩) ([2])
#guard is (SourceTypes.translate ⟨false,[.boolLit false,.null,.boolLit true,.null]⟩) ([0,1,2])
#guard is (SourceTypes.translate ⟨false,[]⟩) ([])
#guard !ok (SourceTypes.translate ⟨true,[]⟩)
#guard !ok (SourceTypes.translate ⟨false,[.str]⟩)
#guard (meet (.boolLit true) (.boolLit false) : List (Clause (List Nat))) == []
#guard (meet .bool (.boolLit true) : List (Clause (List Nat))) == [.boolLit true]

private def G0 := SourceTypes.graph SourceTypes.initial
private def request (t : Tm) (A : Ty Nat) : Request :=
  ⟨SourceTypes.initial, [⟨t,.ret,none⟩], [⟨[],A⟩], A, 0, [], []⟩
#guard ok (produceSourceJson (toJson (request .tru [1])) 5)
#guard ok (produceSourceJson (toJson (request .fls [2])) 5)
#guard ok (produceSourceJson (toJson (request .tru [1,2])) 5)
#guard !ok (produceSourceJson (toJson (request .tru [2])) 5)
#guard !ok (produceSourceJson (toJson (request .fls [1])) 5)

#guard PositiveCertificates.checkClause G0 [] [] [] [] (.boolLit true) .bool
#guard !PositiveCertificates.checkClause G0 [] [] [] [] .bool (.boolLit true)
#guard !PositiveCertificates.checkClause G0 [] [] [] [] (.boolLit true) (.boolLit false)

-- Primitive fixture types use the same JSON schema as real source claims.
private def wireTy (t : Claim.Ty) : Json := Json.mkObj [("top", toJson t.top),
  ("atoms", toJson (t.atoms.map fun a => match a with
    | .null => Json.mkObj [("a",toJson "null")]
    | .bool => Json.mkObj [("a",toJson "boolean")]
    | .boolLit b => Json.mkObj [("a",toJson "booleanlit"),("v",toJson (if b then "true" else "false"))]
    | _ => Json.mkObj [("a",toJson "unsupported")]))]
-- Name resolution after a second binding must select the older slot.
-- Complete producer-neutral claims for literal negation. SKJS may constant-fold
-- these literals without exporting their operand claims; that is an export gap.
private def checkLiteralNegation (q : Bool) : Except String Unit := do
  let result := wireTy ⟨false,[.boolLit (!q)]⟩
  let fn : Fragment.Fn := ⟨"negate",(0,1),[],result,
    [.ret (2,6) (.not (3,6) (.lit (4,6) (.vbool q)))]⟩
  let claims : Fragment.Claims := ⟨"negate",(0,1),[],result,[(2,[])],
    [((3,6),result),((4,6),wireTy ⟨false,[.boolLit q]⟩)]⟩
  let r ← extractFn fn claims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 10)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 10 r.obligations
  pure ()
#guard ok (checkLiteralNegation true)
#guard ok (checkLiteralNegation false)

private def f : Fragment.Fn := ⟨"f",(0,1),[],(wireTy ⟨false,[.boolLit true]⟩),
  [.cst (2,3) "x" none (.lit (4,5) (.vbool true)),
   .cst (6,7) "y" none (.lit (8,9) (.vbool false)),
   .ret (10,11) (.var (12,13) "x")]⟩
private def t : Json := (wireTy ⟨false,[.boolLit true]⟩)
private def b : Json := (wireTy ⟨false,[.boolLit false]⟩)
private def fc : Fragment.Claims := ⟨"f",(0,1),[],t,
  [(2,[]),(6,[("x",t)]),(10,[("x",t),("y",b)])],
  [((4,5),t),((8,9),b),((12,13),t)]⟩
#guard is ((extractFn f fc).map (fun r => r.program[1]?.map ControlFlow.Node.expression)) ((some (.var 1)))
#guard ok (do produceSourceJson (toJson (← extractFn f fc).toRequest) 6)
-- Test execution of this primitive subset uses the calculus's substitution and
-- simultaneous environment transfer. It is a compiler regression, not a source
-- preservation proof or a second maintained evaluator.
private def runPrimitive : Nat → ControlFlow.Program → Nat → Env → Option Tm
  | 0, _, _, _ => none
  | fuel+1, P, label, ρ => do
    let node ← P[label]?
    let v := instantiate 0 ρ node.expression
    if !isVal v then none else
      match node.continuation with
      | .ret => some v
      | .bind next => runPrimitive fuel P next.label (PointClaims.mapEnv next.mapping (push v ρ))
      | .effect next => runPrimitive fuel P next.label (PointClaims.mapEnv next.mapping ρ)
      | .branch yes no =>
        let target ← match v with | .tru => some yes | .fls => some no | _ => none
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping ρ)
      | .branchBind yes no =>
        let target ← match v with | .tru => some yes | .fls => some no | _ => none
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping (push v ρ))
      | .tagBind tag yes no =>
        let target := if tagHolds tag v then yes else no
        runPrimitive fuel P target.label (PointClaims.mapEnv target.mapping (push v ρ))

private def runRequest (r : SourceRequest) : Option Tm := runPrimitive 100 r.program r.start (fun _ => .nul)

private def branchFn (q : Bool) : Fragment.Fn :=
  ⟨"branch",(0,1),[],t,
    [.cst (2,3) "outer" none (.lit (4,5) (.vbool true)),
     .ite (6,17) (.lit (8,9) (.vbool q))
       [.cst (10,11) "local" none (.lit (12,13) (.vbool false))]
       (some [.cst (14,15) "local" none (.lit (16,17) .vnull)]),
     .ret (18,21) (.var (20,21) "outer")]⟩
private def branchClaims (q : Bool) : Fragment.Claims :=
  ⟨"branch",(0,1),[],t,
    [(2,[]),(6,[("outer",t)]),(10,[("outer",t)]),
     (14,[("outer",t)]),(18,[("outer",t)])],
    [((4,5),t),((8,9),(wireTy ⟨false,[.boolLit q]⟩)),
     ((12,13),b),((16,17),(wireTy ⟨false,[.null]⟩)),((20,21),t)]⟩

#guard is ((extractFn (branchFn true) (branchClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (branchFn false) (branchClaims false)).map runRequest) (some .tru)
#guard ok (do produceSourceJson (toJson (← extractFn (branchFn true) (branchClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (branchFn false) (branchClaims false)).toRequest) 8)

-- A shared continuation has exactly one return node, with two predecessors
-- reaching its source-expression node. Continuation duplication fails this test.
private def targets : ControlFlow.Continuation → List Nat
  | .ret => []
  | .bind t | .effect t => [t.label]
  | .branch y n | .branchBind y n | .tagBind _ y n => [y.label,n.label]
#guard is ((extractFn (branchFn true) (branchClaims true)).map fun r =>
  (r.program.filter (fun n => n.continuation == .ret)).length) 1
#guard is ((extractFn (branchFn true) (branchClaims true)).map fun r =>
  (r.program.flatMap (fun n => targets n.continuation)).count 1) 2

private def choiceFn (q : Bool) : Fragment.Fn :=
  ⟨"choice",(0,1),[],(wireTy ⟨false,[.bool]⟩),
    [.ite (2,11) (.lit (4,5) (.vbool q))
      [.ret (6,9) (.lit (8,9) (.vbool true))]
      (some [.ret (10,13) (.lit (12,13) (.vbool false))])]⟩
private def choiceClaims (q : Bool) : Fragment.Claims :=
  ⟨"choice",(0,1),[],(wireTy ⟨false,[.bool]⟩),[(2,[]),(6,[]),(10,[])],
    [((4,5),(wireTy ⟨false,[.boolLit q]⟩)),((8,9),t),((12,13),b)]⟩
#guard is ((extractFn (choiceFn true) (choiceClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (choiceFn false) (choiceClaims false)).map runRequest) (some .fls)
#guard ok (do produceSourceJson (toJson (← extractFn (choiceFn true) (choiceClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (choiceFn false) (choiceClaims false)).toRequest) 8)

-- The tested binding is older than another local, so the refinement map must
-- select its copied value rather than refine whichever slot happens to be first.
private def variableFn (q : Bool) : Fragment.Fn :=
  ⟨"variable",(0,1),[],(wireTy ⟨false,[.bool]⟩),
    [.cst (2,3) "tested" (some (wireTy ⟨false,[.bool]⟩)) (.lit (4,5) (.vbool q)),
     .cst (6,7) "other" (some (wireTy ⟨false,[.bool]⟩)) (.lit (8,9) (.vbool false)),
     .ite (10,21) (.var (12,13) "tested")
       [.ret (14,17) (.var (16,17) "tested")]
       (some [.ret (18,21) (.var (20,21) "tested")])]⟩
private def variableClaims (q : Bool) : Fragment.Claims :=
  let bool : Json := (wireTy ⟨false,[.bool]⟩)
  ⟨"variable",(0,1),[],bool,
    [(2,[]),(6,[("tested",bool)]),
     (10,[("tested",bool),("other",bool)]),
     (14,[("tested",t),("other",bool)]),
     (18,[("tested",b),("other",bool)])],
    [((4,5),(wireTy ⟨false,[.boolLit q]⟩)),((8,9),b),
     ((12,13),bool),((16,17),t),((20,21),b)]⟩
#guard is ((extractFn (variableFn true) (variableClaims true)).map runRequest) (some .tru)
#guard is ((extractFn (variableFn false) (variableClaims false)).map runRequest) (some .fls)
#guard ok (do produceSourceJson (toJson (← extractFn (variableFn true) (variableClaims true)).toRequest) 8)
#guard ok (do produceSourceJson (toJson (← extractFn (variableFn false) (variableClaims false)).toRequest) 8)

-- Source input slots follow declaration order, independently of export order
-- inside each environment. Newly declared locals still push ahead of them.
private def parameterFn : Fragment.Fn :=
  ⟨"parameters",(0,1),[⟨"first",(wireTy ⟨false,[.null]⟩),false⟩,⟨"second",(wireTy ⟨false,[.bool]⟩),false⟩],
    (wireTy ⟨false,[.bool]⟩),[.ret (2,5) (.var (4,5) "second")]⟩
private def parameterClaims : Fragment.Claims :=
  ⟨"parameters",(0,1),[("first",(wireTy ⟨false,[.null]⟩)),("second",(wireTy ⟨false,[.bool]⟩))],
    (wireTy ⟨false,[.bool]⟩),
    [(2,[("second",(wireTy ⟨false,[.bool]⟩)),("first",(wireTy ⟨false,[.null]⟩))])],
    [((4,5),(wireTy ⟨false,[.bool]⟩))]⟩
private def runArguments (r : SourceRequest) (vs : List Tm) :=
  runPrimitive 100 r.program r.start (fun i => vs[i]?.getD .nul)
#guard is ((extractFn parameterFn parameterClaims).map (·.inputs)) [[0],[1,2]]
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.tru])) (some .tru)
#guard is ((extractFn parameterFn parameterClaims).map (fun r => runArguments r [.nul,.fls])) (some .fls)
#guard ok (do produceSourceJson (toJson (← extractFn parameterFn parameterClaims).toRequest) 8)

-- Even if all internal claims consistently narrow the parameter to true,
-- the separate source-signature entry edge must reject that narrowing.
private def narrowedEntry : Fragment.Claims := { parameterClaims with
  envs := [(2,[("first",(wireTy ⟨false,[.null]⟩)),("second",t)])]
  exprs := [((4,5),t)] }
#guard !ok (do produceSourceJson (toJson (← extractFn parameterFn narrowedEntry).toRequest) 8)

private def cellWire : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "record"),("fields",toJson [Json.mkObj [("name",toJson "value"),
    ("optional",toJson false),("read",wireTy ⟨false,[.bool]⟩),("write",wireTy ⟨false,[.bool]⟩)]]),
   ("indexes",Json.mkObj [("string",toJson "absent"),("number",toJson "absent"),("symbol",toJson "absent")]),
   ("call",toJson "unknown"),("construct",toJson "unknown"),("array",toJson "unknown")]])]

-- Trace the actual extracted graph: allocate, alias, assign through the alias.
-- Check both the assignment's value and the mutated heap using the existing
-- calculus transitions, without introducing a second evaluator.
private def cellFn : Fragment.Fn :=
  ⟨"cell",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) ["value"] [(.lit (5,6) (.vbool true))]),
     .cst (8,9) "alias" (some cellWire) (.var (10,11) "cell"),
     .ret (12,19) (.write (14,19) "value" (.var (14,15) "alias") (.lit (18,19) (.vbool false))) ]⟩
private def cellClaims : Fragment.Claims :=
  ⟨"cell",(0,1),[],wireTy ⟨false,[.bool]⟩,
   [(2,[]),(8,[("cell",cellWire)]),(12,[("cell",cellWire),("alias",cellWire)])],
   [((4,7),cellWire),((5,6),t),((10,11),cellWire),
    ((14,19),b),((14,15),cellWire),((18,19),b)]⟩
private def cellRequest : Request :=
  (SourceExtraction.extractFn cellFn cellClaims).map (·.toRequest) |>.toOption.getD (request .nul [0])
#guard ok (SourceExtraction.extractFn cellFn cellClaims)
#guard ok (produceSourceJson (toJson cellRequest) 8)

private def cellProgram : ControlFlow.Program :=
  [⟨.var 0,.ret,none⟩,
   ⟨.var 0,.bind ⟨0,some [0,3,4]⟩,none⟩,
   ⟨.write (.var 1) (.var 0),.effect 1,none⟩,
   ⟨.fls,.bind 2,none⟩, ⟨.var 0,.bind 3,none⟩,
   ⟨.var 0,.effect 4,none⟩, ⟨.var 0,.bind 5,none⟩,
   ⟨.var 0,.effect 6,none⟩, ⟨.alloc (.var 0),.bind ⟨7,some [0]⟩,none⟩,
   ⟨.tru,.bind 8,none⟩, ⟨.nul,.effect 9,none⟩]
#guard cellRequest.program == cellProgram
#guard cellRequest.start == 10

theorem cell_assignment_trace : ControlFlow.Execution cellProgram 24 []
    (.at 10 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms cell_assignment_trace

/-- A signature indifferent to its receiver states `unknown` for it. -/
private def unknownWire : Json := Json.mkObj [("top",toJson true),("atoms",toJson ([] : List Json))]
private def functionWire : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "function"),("this",unknownWire),("params",toJson [wireTy ⟨false,[.null]⟩]),
   ("result",wireTy ⟨false,[.bool]⟩),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def captureFn : Fragment.Fn :=
  ⟨"capture",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) ["value"] [(.lit (5,6) (.vbool true))]),
     .cst (8,9) "reader" (some functionWire)
       (.lam (10,15) "unit" (wireTy ⟨false,[.null]⟩) (wireTy ⟨false,[.bool]⟩)
         (.read (12,15) "value" (.var (12,13) "cell"))),
     .cst (16,17) "alias" (some cellWire) (.var (18,19) "cell"),
     .effect (20,25) (.write (20,25) "value" (.var (20,21) "alias") (.lit (24,25) (.vbool false))),
     .ret (26,33) (.app (28,33) (.var (28,29) "reader") (.lit (32,33) .vnull))]⟩
private def captureClaims : Fragment.Claims :=
  let B := wireTy ⟨false,[.bool]⟩
  ⟨"capture",(0,1),[],B,
   [(2,[]),(8,[("cell",cellWire)]),(16,[("cell",cellWire),("reader",functionWire)]),
    (20,[("cell",cellWire),("reader",functionWire),("alias",cellWire)]),
    (26,[("cell",cellWire),("reader",functionWire),("alias",cellWire)])],
   [((4,7),cellWire),((5,6),t),((10,15),functionWire),((12,15),B),((12,13),cellWire),
    ((18,19),cellWire),((20,25),b),((20,21),cellWire),((24,25),b),
    ((28,33),B),((28,29),functionWire),((32,33),wireTy ⟨false,[.null]⟩)]⟩
private def captureRequest : Request :=
  (SourceExtraction.extractFn captureFn captureClaims).map (·.toRequest) |>.toOption.getD (request .nul [0])
#guard ok (SourceExtraction.extractFn captureFn captureClaims)
#guard ok (produceSourceJson (toJson captureRequest) 10)
private def captureProgram : ControlFlow.Program :=
  [⟨.var 0,.ret,none⟩, ⟨.app (.var 1) (.var 0),.bind ⟨0,some [0,3,4,5]⟩,none⟩,
   ⟨.nul,.bind 1,none⟩, ⟨.var 1,.bind 2,none⟩,
   ⟨.var 0,.bind ⟨3,some [3,4,5]⟩,none⟩, ⟨.write (.var 1) (.var 0),.effect 4,none⟩,
   ⟨.fls,.bind 5,none⟩, ⟨.var 0,.bind 6,none⟩, ⟨.var 0,.effect 7,none⟩, ⟨.var 1,.bind 8,none⟩,
   ⟨.var 0,.effect 9,none⟩, ⟨.funE (.read (.var 2)),.bind 10,none⟩,
   ⟨.var 0,.effect 11,none⟩, ⟨.alloc (.var 0),.bind ⟨12,some [0]⟩,none⟩,
   ⟨.tru,.bind 13,none⟩, ⟨.nul,.effect 14,none⟩]
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard captureRequest.start == 15

/-- The extracted closure reads after the alias write and returns false.
The graph-equality guards above tie this trace to the source compiler regression. -/
theorem captured_alias_trace : ControlFlow.Execution captureProgram 37 []
    (.at 15 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms captured_alias_trace

-- A terminal closure branch adds one conditional step, with each arm occurring
-- once. The condition reads the heap at call time, after the alias write.
private def branchCaptureFn : Fragment.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .constants pos [⟨name, np, annot, .lam lp param arg ret body⟩] =>
      .constants pos [⟨name, np, annot, (.lam lp param arg ret
        (.block (40,49) [.ite (40,49) body
          [.ret (41,44) (.lit (42,43) (.vbool true))]
          (some [.ret (45,48) (.lit (46,47) (.vbool false))])]))⟩]
    | st => st }
private def branchCaptureClaims : Fragment.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(41,H),(45,H)]
    exprs := captureClaims.exprs ++ [((42,43),t),((46,47),b)] }
private def branchCaptureProgram : ControlFlow.Program :=
  captureProgram.set 11 ⟨.funE (.ite (.read (.var 2)) .tru .fls),.bind 10,none⟩
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard ok (do
  let r ← extractFn branchCaptureFn branchCaptureClaims
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem terminal_branch_trace : ControlFlow.Execution branchCaptureProgram 38 []
    (.at 15 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.iteC (.readV rfl)))
    | apply ControlFlow.Execution.next (.expr .iteF)
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms terminal_branch_trace

-- Both arms complete before the shared read; the false arm changes the cell
-- to true. Branch-local administrative slots cannot shift the continuation.
private def joinedCaptureFn : Fragment.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .constants pos [⟨name, np, annot, .lam lp param arg ret body⟩] =>
      .constants pos [⟨name, np, annot, (.lam lp param arg ret
        (.block (40,53)
          [.ite (40,49) body []
            (some [.effect (43,48)
              (.write (44,47) "value" (.var (44,45) "cell") (.lit (46,47) (.vbool true)))]),
           .ret (50,53) (.read (51,53) "value" (.var (51,52) "cell"))]))⟩]
    | st => st }
private def joinedCaptureClaims : Fragment.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(43,H),(50,H)]
    exprs := captureClaims.exprs ++ [((44,47),t),((44,45),cellWire),((46,47),t),
      ((51,53),wireTy ⟨false,[.bool]⟩),((51,52),cellWire)] }
private def joinedCaptureProgram : ControlFlow.Program :=
  let assignment := Tm.letE (.var 2) (.letE .tru (.letE (.write (.var 1) (.var 0)) (.var 1)))
  captureProgram.set 11
    ⟨.funE (.letE (.ite (.read (.var 2)) .nul (.letE assignment .nul))
      (.read (.var 3))),.bind 10,none⟩
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard ok (do
  let r ← extractFn joinedCaptureFn joinedCaptureClaims
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem shared_continuation_trace : ControlFlow.Execution joinedCaptureProgram 45 []
    (.at 15 (fun _ => .nul)) [.tru,.nul] (.done .tru) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.letV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.letC (.iteC (.readV rfl))))
    | apply ControlFlow.Execution.next (.expr (.letC .iteF))
    | apply ControlFlow.Execution.next (.expr (.letC (.letC (.letV rfl))))
    | apply ControlFlow.Execution.next (.expr (.letC (.letC (.letC (.writeV rfl (by decide))))))
    | apply ControlFlow.Execution.next (.expr (.letC (.letV rfl)))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms shared_continuation_trace

-- The same extracted conditional must skip its continuation on early return.
private def earlyCaptureFn (q : Bool) : Fragment.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .constants pos [⟨name, np, annot, .lam lp param arg ret body⟩] =>
      .constants pos [⟨name, np, annot, (.lam lp param arg ret
        (.block (40,59) [.ite (40,59) body
          [.ret (41,44) (.lit (42,43) (.vbool true))]
          (some [.effect (45,50)
              (.write (46,49) "value" (.var (46,47) "cell") (.lit (48,49) (.vbool false))),
            .ret (52,55) (.read (53,55) "value" (.var (53,54) "cell"))])]))⟩]
    | .effect pos (.write wp fld receiver (.lit lp _)) =>
      .effect pos (.write wp fld receiver (.lit lp (.vbool q)))
    | st => st }
private def earlyCaptureClaims (q : Bool) : Fragment.Claims :=
  let H := [("unit",wireTy ⟨false,[.null]⟩),("cell",cellWire)]
  { captureClaims with
    envs := captureClaims.envs ++ [(40,H),(41,H),(45,H),(52,H)]
    exprs := (captureClaims.exprs.map fun (pos,A) =>
      (pos,if pos == (24,25) || pos == (20,25) then (if q then t else b) else A)) ++
      [((42,43),t),((46,49),b),((46,47),cellWire),((48,49),b),
       ((53,55),wireTy ⟨false,[.bool]⟩),((53,54),cellWire)] }
private def earlyCaptureProgram (q : Bool) : ControlFlow.Program :=
  let assignment := Tm.letE (.var 2) (.letE .fls (.letE (.write (.var 1) (.var 0)) (.var 1)))
  (captureProgram.set 6 ⟨if q then .tru else .fls,.bind 5,none⟩).set 11
    ⟨.funE (.ite (.read (.var 2)) .tru
      (.letE (.letE assignment .nul) (.read (.var 3)))),.bind 10,none⟩
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard [true,false].all fun q => ok (do
  let r ← extractFn (earlyCaptureFn q) (earlyCaptureClaims q)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

theorem early_return_trace (q : Bool) : ControlFlow.Execution (earlyCaptureProgram q)
    (if q then 38 else 45) [] (.at 15 (fun _ => .nul))
    [if q then .tru else .fls,.nul] (.done (if q then .tru else .fls)) := by
  cases q <;> repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.writeV rfl (by decide)))
    | apply ControlFlow.Execution.next (.expr (.letV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.iteC (.readV rfl)))
    | apply ControlFlow.Execution.next (.expr .iteT)
    | apply ControlFlow.Execution.next (.expr .iteF)
    | apply ControlFlow.Execution.next (.expr (.letC (.letC (.letV rfl))))
    | apply ControlFlow.Execution.next (.expr (.letC (.letC (.letC (.writeV rfl (by decide))))))
    | apply ControlFlow.Execution.next (.expr (.letC (.letV rfl)))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms early_return_trace

-- Supplemental proofs are necessary even when the whole lambda is typable.
private def captureRequired := (extractFn captureFn captureClaims).toOption.getD ⟨captureRequest,[],[],[],[],[], [], []⟩
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard ok (ExpressionClaims.produce (RequestJson.graph captureRequest)
  captureRequired.searchLabels captureRequest.types.length 10 captureRequired.obligations)
private def narrowedCapture : Fragment.Claims :=
  { captureClaims with exprs := captureClaims.exprs.map fun (pos,ty) =>
    (pos, if pos == (12,15) then t else ty) }
-- The narrowed claim is a node of the closure's graph code: its search, not
-- a supplemental proof, rejects it.
#guard !ok (do produceSourceJson (toJson (← extractFn captureFn narrowedCapture).toRequest) 10)

private def writerFn : Fragment.Fn :=
  ⟨"writer",(0,1),[],wireTy ⟨false,[.bool]⟩,
    [.cst (2,3) "cell" (some cellWire) (.alloc (4,7) ["value"] [(.lit (5,6) (.vbool true))]),
     .cst (8,9) "writer" (some functionWire)
       (.lam (10,19) "unit" (wireTy ⟨false,[.null]⟩) (wireTy ⟨false,[.bool]⟩)
         (.write (12,19) "value" (.var (12,13) "cell") (.lit (18,19) (.vbool false)))),
     .ret (20,27) (.app (22,27) (.var (22,23) "writer") (.lit (26,27) .vnull))]⟩
private def writerClaims : Fragment.Claims :=
  ⟨"writer",(0,1),[],wireTy ⟨false,[.bool]⟩,
   [(2,[]),(8,[("cell",cellWire)]),(20,[("cell",cellWire),("writer",functionWire)])],
   [((4,7),cellWire),((5,6),t),((10,19),functionWire),((12,19),b),
    ((12,13),cellWire),((18,19),b),((22,27),wireTy ⟨false,[.bool]⟩),
    ((22,23),functionWire),((26,27),wireTy ⟨false,[.null]⟩)]⟩
private def writerProgram : ControlFlow.Program :=
  [⟨.var 0,.ret,none⟩, ⟨.app (.var 1) (.var 0),.bind ⟨0,some [0,3,4]⟩,none⟩,
   ⟨.nul,.bind 1,none⟩, ⟨.var 0,.bind 2,none⟩, ⟨.var 0,.effect 3,none⟩,
   ⟨.funE (.letE (.var 2) (.letE .fls (.letE (.write (.var 1) (.var 0)) (.var 1)))),.bind 4,none⟩,
   ⟨.var 0,.effect 5,none⟩, ⟨.alloc (.var 0),.bind ⟨6,some [0]⟩,none⟩,
   ⟨.tru,.bind 7,none⟩, ⟨.nul,.effect 8,none⟩]
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
#guard is ((extractFn writerFn writerClaims).map (·.start)) 9
#guard ok (do
  let r ← extractFn writerFn writerClaims
  let _ ← produceSourceJson (toJson r.toRequest) 10
  ExpressionClaims.produce (RequestJson.graph r.toRequest) r.searchLabels r.types.length 10 r.obligations)

/-- Calling the extracted writer changes the heap and returns its RHS, not null. -/
theorem closure_write_trace : ControlFlow.Execution writerProgram 27 []
    (.at 9 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.letV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.letC (.writeV rfl (by decide))))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms closure_write_trace

-- A single-return block has the same execution as its expression body, but
-- adds proof obligations for the supplied statement environment.
private def blockCaptureFn : Fragment.Fn :=
  { captureFn with body := captureFn.body.map fun st => match st with
    | .constants pos [⟨name, np, annot, .lam lp param arg ret body⟩] =>
      .constants pos [⟨name, np, annot, (.lam lp param arg ret (.block (11,16) [.ret (11,16) body]))⟩]
    | st => st }
private def blockCaptureClaims (unitTy : Json) : Fragment.Claims :=
  { captureClaims with envs := captureClaims.envs ++
    [(11,[("unit",unitTy),("cell",cellWire)])] }
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
private def blockObligations (unitTy : Json) : Except String Unit := do
  let r ← extractFn blockCaptureFn (blockCaptureClaims unitTy)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 10 r.obligations
  let _ ← produceSourceJson (toJson r.toRequest) 10
  pure ()
#guard ok (blockObligations (wireTy ⟨false,[.null]⟩))
-- Forgetting parameter precision is allowed; inventing an unused type is not.
#guard ok (blockObligations (wireTy ⟨false,[.null,.bool]⟩))
#guard !ok (blockObligations t)
#guard !ok (extractFn blockCaptureFn captureClaims)

private def localWriterFn : Fragment.Fn :=
  { writerFn with body := writerFn.body.map fun st => match st with
    | .constants pos [⟨name, np, annot, .lam lp param arg ret _⟩] =>
      .constants pos [⟨name, np, annot, (.lam lp param arg ret
        (.block (30,43)
          [.constants (30,31) [⟨"saved", (30,31), some (wireTy ⟨false,[.bool]⟩), .lit (32,33) (.vbool false)⟩],
           .effect (34,35) (.write (36,39) "value" (.var (36,37) "cell") (.var (38,39) "saved")),
           .ret (40,43) (.read (41,43) "value" (.var (41,42) "cell"))]))⟩]
    | st => st }
private def localWriterClaims : Fragment.Claims :=
  let N := wireTy ⟨false,[.null]⟩
  let B := wireTy ⟨false,[.bool]⟩
  { writerClaims with
    envs := writerClaims.envs ++
      [(30,[("unit",N),("cell",cellWire)]),
       (34,[("unit",N),("cell",cellWire),("saved",B)]),
       (40,[("unit",N),("cell",cellWire),("saved",B)])]
    exprs := writerClaims.exprs ++
      [((32,33),b),((36,39),B),((36,37),cellWire),((38,39),B),
       ((41,43),B),((41,42),cellWire)] }
private def localWriterProgram : ControlFlow.Program :=
  let write : Tm := .letE (.var 3) (.letE (.var 1) (.letE (.write (.var 1) (.var 0)) (.var 1)))
  writerProgram.set 5
    ⟨.funE (.letE .fls (.letE write (.read (.var 4)))),.bind 4,none⟩
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.

/-- A saved local is used by the write and survives the anonymous effect slot. -/
theorem local_writer_trace : ControlFlow.Execution localWriterProgram 30 []
    (.at 9 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  repeat first
    | exact ControlFlow.Execution.refl
    | apply ControlFlow.Execution.next (.enter rfl)
    | apply ControlFlow.Execution.next (.expr (.makeV rfl))
    | apply ControlFlow.Execution.next (.expr (.letV rfl))
    | apply ControlFlow.Execution.next (.expr (.beta rfl))
    | apply ControlFlow.Execution.next (.expr (.letC (.letV rfl)))
    | apply ControlFlow.Execution.next (.expr (.letC (.letC (.writeV rfl (by decide)))))
    | apply ControlFlow.Execution.next (.expr (.readV rfl))
    | apply ControlFlow.Execution.next (.bind rfl)
    | apply ControlFlow.Execution.next (.effect rfl)
    | apply ControlFlow.Execution.next (.ret rfl)

#print axioms local_writer_trace

-- A suggested intermediate type cannot turn false into true.
#guard !(CertificateProducer.expressionWith G0 [[1],[2],[1,2]]
  [⟨[],.fls,[1]⟩] 4 [] (.letE .fls (.var 0)) [1]).isSome

-- Direct recipes preserve supplied types while rebuilding proofs in the actual context.
private def widenedVariable := DirectProof.var [[1,2]] 0 [1,2]
#guard ((DirectProof.render G0 [[1],[2],[1,2]] [[2]] widenedVariable).map
  (fun e => ProgramCertificates.checkTree G0 e)) == some true
#guard !(DirectProof.render G0 [[1],[2],[1,2]] [[2]]
  (DirectProof.var [[1]] 0 [1])).isSome

-- All supported closure obligations now have recipes and require no expression-search fuel.
#guard ok (do
  let r ← extractFn localWriterFn localWriterClaims
  if r.obligations.any (fun q => q.plan.isNone) then throw "missing recipe"
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  pure ())

-- A forged recipe or reused certificate is still rejected by the ordinary checker.
private def forged : ProgramCertificates.Evidence Nat :=
  .node ⟨[],.fls,[1]⟩ .truLit []
#guard !ok (produceSourceJson (toJson (request .fls [1])) 4 [] [forged])
#guard !ok (ExpressionClaims.produce G0 [0,1,2,3] SourceTypes.initial.length 4
  [⟨(0,1),⟨[],.fls,[1]⟩,some (DirectProof.node [] .fls [1] .truLit),"expression-claim",[]⟩])

-- Source unions compose already-supported atoms, preserving every arm's checks.
-- Each compound arm is interned once, at the first free label.
private def joined (types : List Json) : Json := Json.mkObj [
  ("top",toJson false), ("atoms",toJson (types.flatMap fun j =>
    ((jArr j "atoms").toOption.getD [])))]
private def lowered (j : Json) : Except String (Ty Nat) :=
  (Fragment.translate j).run' SourceTypes.initial
#guard is (lowered (joined [wireTy ⟨false,[.null]⟩,cellWire])) [0,4]
#guard is (lowered (joined [cellWire,wireTy ⟨false,[.null]⟩,cellWire])) [0,4]
-- A function type's receiver is interned before its signature.
#guard is (lowered (joined [wireTy ⟨false,[.null]⟩,functionWire])) [0,5]
#guard is (lowered (joined [cellWire,functionWire])) [4,6]
#guard !ok (lowered (joined [cellWire,wireTy ⟨false,[.str]⟩]))
-- `unknown` is semantic top: one interned label, past the four fixed ones.
#guard is (lowered (Json.mkObj [("top",toJson true),("atoms",toJson ([] : List Json))])) [4]

-- An input is assumed at its annotation whatever its type: a nullable cell
-- parameter is admitted like a primitive or an arrow.
private def nullableCell : Json := joined [wireTy ⟨false,[.null]⟩,cellWire]
private def externalFn : Fragment.Fn :=
  { branchFn true with params := [⟨"external",nullableCell,false⟩] }
private def externalEnvs : List (Nat × List (String × Json)) :=
  (branchClaims true).envs.map fun pv => (pv.1,("external",nullableCell) :: pv.2)
private def externalClaims : Fragment.Claims :=
  { branchClaims true with params := [("external",nullableCell)], envs := externalEnvs }
#guard ok (extractFn externalFn externalClaims)
#guard ok (do produceSourceJson (toJson (← extractFn externalFn externalClaims).toRequest) 8)
#guard !ok (lowered (joined [wireTy ⟨false,[.str]⟩,cellWire]))

-- A graph-safe certificate can still violate the source's local interfaces.
-- This specifically tests the consumer, independently of producer scheduling.
private def localFn : Fragment.Fn :=
  ⟨"local",(0,1),[],wireTy ⟨false,[.boolLit true]⟩,
    [.cst (2,3) "x" (some (wireTy ⟨false,[.bool]⟩)) (.lit (4,5) (.vbool true)),
     .ret (6,9) (.var (8,9) "x")]⟩
private def localClaims : SourceClaims.Function := {
  name := "local", namePos := (0,1), params := [], ret := .ok [1]
  envs := [(2,[]),(6,[("x",.ok [1,2])])]
  exprs := [((4,5),.ok [1]),((8,9),.ok [1,2])] }
private def localRequest := (extractNormalizedFn SourceTypes.initial localFn localClaims).toOption.getD ⟨request .nul [0],[],[],[],[],[], [], []⟩
private def localCertificate (cuts : List Nat) :=
  CertificateProducer.produce (RequestJson.graph localRequest.toRequest)
    localRequest.searchLabels 8 localRequest.result localRequest.program localRequest.claims
    localRequest.start [] localRequest.inputs [] [] localRequest.assertions cuts
private def globalCertificate := (localCertificate []).toOption.get!
#guard RequestJson.verify localRequest.toRequest ⟨globalCertificate, []⟩
#guard !checkAssertions localRequest ⟨globalCertificate, []⟩
#guard (localCertificate localRequest.cuts).toOption.isNone
private def repairedLocal := (extractNormalizedFn SourceTypes.initial localFn
  {localClaims with envs := [(2,[]),(6,[("x",.ok [1])])]}).toOption.getD ⟨request .nul [0],[],[],[],[],[], [], []⟩
#guard ok (RequestJson.produceJson (toJson repairedLocal.toRequest) 8 [] []
  repairedLocal.sourceMap (some repairedLocal.searchLabels) repairedLocal.assertions repairedLocal.cuts)

-- Conjunction is one row whatever its arity. Record conjuncts meet as one
-- record whose fields are sorted and deduplicated, so a repeated contract is
-- the plain cell; overload order is kept, so the two spellings of an arrow
-- pair are two rows.
private def conjoined (j : Json) (others : List Json) : Json :=
  let atom := ((jArr j "atoms").toOption.getD []).headD .null
  let more := others.map fun o => ((jArr o "atoms").toOption.getD []).headD .null
  Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
    (((atom.getObj?).toOption.map (·.toList)).getD [] ++ [("and",toJson more)])])]
private def cellOf (A : Claim.Ty) : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "record"),("fields",toJson [Json.mkObj [("name",toJson "value"),
    ("optional",toJson false),("read",wireTy A),("write",wireTy A)]]),
   ("indexes",Json.mkObj [("string",toJson "absent"),("number",toJson "absent"),("symbol",toJson "absent")]),
   ("call",toJson "unknown"),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def arrowOf (D R : Claim.Ty) : Json := Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj
  [("a",toJson "function"),("this",unknownWire),("params",toJson [wireTy D]),
   ("result",wireTy R),("construct",toJson "unknown"),("array",toJson "unknown")]])]
private def rowOf (j : Json) : Option (List (Clause (List Nat))) :=
  ((Fragment.translate j).run SourceTypes.initial).toOption.bind fun (A,T) => A.head?.bind fun i => (T[i]?).map RequestJson.Row.union
#guard rowOf (conjoined cellWire [cellWire,cellWire]) == some [.refs [("value", [1,2])] [] []]
#guard rowOf (conjoined (cellOf ⟨false,[.boolLit true]⟩) [cellOf ⟨false,[.null]⟩,cellOf ⟨false,[.bool]⟩])
  == some [.refs [("value", [0]),("value",[1]),("value",[1,2])] [] []]
#guard rowOf (conjoined (cellOf ⟨false,[.bool]⟩) [cellOf ⟨false,[.null]⟩,cellOf ⟨false,[.boolLit true]⟩])
  == some [.refs [("value", [0]),("value",[1]),("value",[1,2])] [] []]
private def trueToNull := arrowOf ⟨false,[.boolLit true]⟩ ⟨false,[.null]⟩
private def falseToNull := arrowOf ⟨false,[.boolLit false]⟩ ⟨false,[.null]⟩
#guard rowOf (conjoined trueToNull [falseToNull]) == some [.arrs [([4],[[1]],[0]),([4],[[2]],[0])] []]
#guard rowOf (conjoined falseToNull [trueToNull]) == some [.arrs [([4],[[2]],[0]),([4],[[1]],[0])] []]
#guard rowOf (conjoined trueToNull [trueToNull]) == some [.arrs [([4],[[1]],[0])] []]

-- A lambda claimed at two signatures is proved once per signature; the call
-- resolves to the first signature admitting its argument.
private def overloadWire := conjoined trueToNull [falseToNull]
private def overloadFn : Fragment.Fn :=
  ⟨"overload",(0,1),[],wireTy ⟨false,[.null]⟩,
    [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.bool]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
     .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) (.vbool true)))]⟩
private def overloadClaims : Fragment.Claims :=
  ⟨"overload",(0,1),[],wireTy ⟨false,[.null]⟩,[(2,[]),(10,[("f",overloadWire)])],
   [((4,9),overloadWire),((8,9),wireTy ⟨false,[.null]⟩),((12,17),wireTy ⟨false,[.null]⟩),
    ((12,13),overloadWire),((14,15),t)]⟩
#guard ok (extractFn overloadFn overloadClaims)
#guard ok (do
  let r ← extractFn overloadFn overloadClaims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 10)
  let _ ← ExpressionClaims.produce (RequestJson.graph r.toRequest) r.searchLabels r.types.length 0 r.obligations
  pure ())
-- A claimed signature outside the annotated parameter is refused.
#guard (match extractFn
    { overloadFn with body := [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.boolLit true]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
      .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) (.vbool true)))] } overloadClaims with
  | .error e => e == "closure signature claim is outside the source annotation"
  | .ok _ => false)
-- An argument no signature admits fails the call's claim, not silently.
#guard !ok (do
  let r ← extractFn { overloadFn with body := [.cst (2,3) "f" (some overloadWire)
      (.lam (4,9) "x" (wireTy ⟨false,[.bool]⟩) (wireTy ⟨false,[.null]⟩) (.lit (8,9) .vnull)),
      .ret (10,17) (.app (12,17) (.var (12,13) "f") (.lit (14,15) .vnull))] }
    { overloadClaims with exprs := overloadClaims.exprs.map fun (pos,ty) =>
      (pos, if pos == (14,15) then wireTy ⟨false,[.null]⟩ else ty) }
  produceSourceJson (toJson r.toRequest) 8)

-- An arrow parameter is assumed at its annotation and may be called; a claim
-- that contradicts the annotation is refused by name, and a cell parameter
-- claimed as an arrow where it is called is refused by proof search.
private def callerFn : Fragment.Fn :=
  ⟨"caller",(0,1),[⟨"a",trueToNull,false⟩],wireTy ⟨false,[.null]⟩,
    [.ret (2,9) (.app (4,9) (.var (4,5) "a") (.lit (6,7) (.vbool true)))]⟩
private def callerClaims : Fragment.Claims :=
  ⟨"caller",(0,1),[("a",trueToNull)],wireTy ⟨false,[.null]⟩,[(2,[("a",trueToNull)])],
   [((4,9),wireTy ⟨false,[.null]⟩),((4,5),trueToNull),((6,7),t)]⟩
#guard is ((extractFn callerFn callerClaims).map (·.inputs.length)) 1
#guard ok (do
  let r ← extractFn callerFn callerClaims
  let j := toJson r.toRequest
  verifyJson j (← produceSourceJson j 8))
#guard (match extractFn callerFn { callerClaims with params := [("a",wireTy ⟨false,[]⟩)] } with
  | .error e => e == "claimed parameter type differs from the source annotation for 'a'"
  | .ok _ => false)
#guard !ok (do
  let r ← extractFn { callerFn with params := [⟨"a",cellWire,false⟩] } { callerClaims with params := [("a",cellWire)] }
  produceSourceJson (toJson r.toRequest) 8)

-- Entry allocation replaces exactly the assigned parameter slots. The middle
-- parameter stays a value; both private cells start with their own argument.
private def assignedParametersFn : Fragment.Fn :=
  let B := wireTy ⟨false,[.bool]⟩
  ⟨"parameters",(0,1),[⟨"x",B,false⟩,⟨"keep",B,false⟩,⟨"z",B,false⟩],B,
    [.effect (2,5) (.assign (2,5) "x" (2,3) (.var (4,5) "z")),
     .effect (6,9) (.assign (6,9) "z" (6,7) (.lit (8,9) (.vbool false))),
     .ret (10,13) (.var (12,13) "x")]⟩
private def assignedParametersClaims : Fragment.Claims :=
  let B := wireTy ⟨false,[.bool]⟩
  let H := [("x",B),("keep",B),("z",B)]
  ⟨"parameters",(0,1),H,B,[(2,H),(6,H),(10,H)],
    [((2,5),B),((4,5),B),((6,9),B),((8,9),b),((12,13),B)]⟩
#guard ok (do
  let r ← extractFn assignedParametersFn assignedParametersClaims
  if r.inputs != [[1,2],[1,2],[1,2]] then throw "changed public parameter contract"
  match r.program.reverse with
  | ⟨.nul,.effect entry,none⟩ ::
    ⟨.makeAt .absent ["value"] [.var 0],.bind first,none⟩ ::
    ⟨.makeAt .absent ["value"] [.var 2],.bind second,none⟩ :: _ =>
    if entry.label != r.start-1 || first.label != r.start-2 ||
       first.mapping != some [0,2,3] || second.mapping != some [1,2,0] then
      throw "parameter allocation permuted or aliased the source bindings"
  | _ => throw "parameter allocation did not initialize the assigned slots")

-- A short-circuit lowering can remain well typed even if its branches are
-- accidentally reversed. Check the extracted graph's evaluation shape too.
private def reachesWrite (P : ControlFlow.Program) : Nat → Nat → Bool
  | 0, _ => false
  | fuel+1, label => match P[label]? with
    | none => false
    | some node => match node.expression with
      | .writeAt .. => true
      | _ => (CertificateProducer.successors node.continuation).any
          (fun target => reachesWrite P fuel target.label)

private def nullishAssignmentFn : Fragment.Fn :=
  let B := wireTy ⟨false,[.bool,.null]⟩
  ⟨"fallback",(0,1),[⟨"x",B,false⟩],wireTy ⟨false,[.bool]⟩,
    [.ret (2,7) (.nullishAssign (3,7) "x" (3,4) (.lit (6,7) (.vbool true)))]⟩
private def nullishAssignmentClaims : Fragment.Claims :=
  let B := wireTy ⟨false,[.bool,.null]⟩
  let R := wireTy ⟨false,[.bool]⟩
  ⟨"fallback",(0,1),[("x",B)],R,[(2,[("x",B)])],
    [((3,7),R),((3,4),B),((6,7),t)]⟩
#guard ok (do
  let r ← extractFn nullishAssignmentFn nullishAssignmentClaims
  if (r.program.filter fun n => match n.expression with | .readAt .. => true | _ => false).length != 1 then
    throw "nullish assignment must read its target once"
  let dispatch := r.program.filterMap fun n => match n.continuation with
    | .tagBind .isNullish yes no => some (yes,no)
    | _ => none
  let [(yes,no)] := dispatch | throw "expected one nullish dispatch"
  if yes.mapping != some [0,2] || no.mapping != some [0,2] then
    throw "nullish dispatch must keep the witness and discard the older read"
  if !reachesWrite r.program r.program.length yes.label ||
     reachesWrite r.program r.program.length no.label then
    throw "only the nullish arm may evaluate the assignment")

-- Delaying literal-closure allocations must preserve the order of executing
-- defaults. Two forward captures become available between the effects, and
-- each parameter occurs exactly once in the resulting schedule.
private def scheduledParameters : List (String × Json) :=
  ["first", "second", "before", "later", "after"].map (·, Json.null)
private def scheduledDefaults : List (Nat × Fragment.Expr) :=
  [(0, .lambda (1,2) none [] [] [] false Json.null (.var (1,2) "second")),
   (1, .lambda (3,4) none [] [] [] false Json.null (.var (3,4) "later")),
   (2, .write (5,6) "value" (.var (5,6) "cell") (.lit (5,6) (.vbool false))),
   (3, .read (7,8) "value" (.var (7,8) "cell")),
   (4, .write (9,10) "value" (.var (9,10) "cell") (.lit (9,10) (.vbool true)))]
#guard is (Fragment.parameterOrder scheduledParameters scheduledDefaults) [2,3,1,0,4]
-- Reading, invoking or exposing a pending closure must fail even though its
-- eventual function type is valid. Capture cycles cannot be scheduled either.
#guard !ok (Fragment.parameterOrder scheduledParameters
  (scheduledDefaults.map fun (i,e) => (i, if i == 3 then
    .call (7,8) (.var (7,8) "first") [] [] [] else e)))
#guard !ok (Fragment.parameterOrder scheduledParameters
  (scheduledDefaults.map fun (i,e) => (i, if i == 1 then
    .lambda (3,4) none [] [] [] false Json.null (.var (3,4) "first") else e)))

end Verification.Model.SourceExtractionTests
