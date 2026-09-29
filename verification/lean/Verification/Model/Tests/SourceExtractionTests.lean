import Verification.Model.Source.SourceClaimJson

namespace Verification.Model.SourceExtractionTests
open Lean PositiveNormalization ProgramTyping RequestJson SourceExtraction

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

private def is [BEq α] (r : Except String α) (expected : α) : Bool :=
  match r with | .ok a => a == expected | .error _ => false

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

#guard (meet (.boolLit true) (.boolLit false) : List (Clause (List Nat))) == []
#guard (meet .bool (.boolLit true) : List (Clause (List Nat))) == [.boolLit true]

/-- The four primitive values, labels 0 to 3. -/
private def G0 : PositiveGraphs.NormalGraph Nat :=
  .ofRows fun i => ([[.nul], [.boolLit true], [.boolLit false], [.undef]] :
    List (List (Clause (List Nat))))[i]?.getD []
#guard PositiveCertificates.checkClause G0 [] [] [] [] (.boolLit true) .bool
#guard !PositiveCertificates.checkClause G0 [] [] [] [] .bool (.boolLit true)
#guard !PositiveCertificates.checkClause G0 [] [] [] [] (.boolLit true) (.boolLit false)

-- A suggested intermediate type cannot turn false into true.
#guard !(CertificateProducer.expressionWith G0 [[1],[2],[1,2]]
  [⟨[],.fls,[1]⟩] 4 [] (.letE .fls (.var 0)) [1]).isSome

-- Direct recipes preserve supplied types while rebuilding proofs in the actual context.
private def widenedVariable := DirectProof.var [[1,2]] 0 [1,2]
#guard ((DirectProof.render G0 [[1],[2],[1,2]] [[2]] widenedVariable).map
  (fun e => ProgramCertificates.checkTree G0 e)) == some true
#guard !(DirectProof.render G0 [[1],[2],[1,2]] [[2]]
  (DirectProof.var [[1]] 0 [1])).isSome

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


/-! ### Lowering, on the pipeline's own documents

`SourceExtraction/lowering-slots.*.json` are the parser's fragment and the
OCaml producer's claims for `ocaml-producer/examples/lowering-slots.ts`, whose
pipeline case verifies them. The guards below run the programs extraction
lowers from them, check the shape of what no type observes, and refuse claims
no producer writes. -/

private def slotsFile : String := "verification/ocaml-producer/examples/lowering-slots.ts"
private def slotsAst : Json :=
  (Json.parse (include_str "SourceExtraction/lowering-slots.fragment.json")).toOption.getD .null
private def slotsClaims : Json :=
  (Json.parse (include_str "SourceExtraction/lowering-slots.claims.json")).toOption.getD .null

/-- The request extracted for the function of that name. -/
private def unit (name : String) : Option (SourceRequest EquationStore.State EquationGraphs.Tree) := do
  let rs ← (SourceClaimJson.extractGraphRequests slotsAst slotsClaims slotsFile).toOption
  let fs ← (slotsAst.getObjValAs? (List Json) "functions").toOption
  let i ← fs.findIdx? fun f => (f.getObjValAs? String "name").toOption == some name
  rs[i]?

/-- The value a lowered function returns on these arguments. -/
private def runs (name : String) (args : List Tm) : Option Tm := do
  let r ← unit name
  runPrimitive 100 r.program r.start (fun i => args[i]?.getD .nul)

-- A name resolves to its own slot past a later binding; an arm's binding of
-- one name stays in its arm; a guard refines the binding it tests, older than
-- a later local; parameters take their slots in declaration order.
#guard runs "olderSlot" [] == some .tru
#guard runs "branchLocals" [.tru] == some .tru
#guard runs "branchLocals" [.fls] == some .tru
#guard runs "refinesOlder" [.tru] == some .tru
#guard runs "refinesOlder" [.fls] == some .fls
#guard runs "parameterSlots" [.nul, .tru] == some .tru
#guard runs "parameterSlots" [.nul, .fls] == some .fls

-- Entry allocation replaces exactly the assigned parameter slots. The middle
-- parameter stays a value; both private cells start with their own argument.
#guard match unit "assignedParameters" with
  | some r => match r.program.reverse with
    | ⟨.nul, .effect entry, none⟩ ::
      ⟨.makeAt .absent ["value"] [.var 0], .bind first, none⟩ ::
      ⟨.makeAt .absent ["value"] [.var 2], .bind second, none⟩ :: _ =>
      entry.label == r.start - 1 && first.label == r.start - 2 &&
        first.mapping == some [0, 2, 3] && second.mapping == some [1, 2, 0]
    | _ => false
  | none => false

-- `??=` reads its target once, dispatches on nullishness keeping the read and
-- dropping the older one, and evaluates the assignment on the nullish arm only.
private def reachesWrite (P : ControlFlow.Program) : Nat → Nat → Bool
  | 0, _ => false
  | fuel+1, label => match P[label]? with
    | none => false
    | some node => match node.expression with
      | .writeAt .. => true
      | _ => (CertificateProducer.successors node.continuation).any
          (fun target => reachesWrite P fuel target.label)
#guard match unit "nullishFallback" with
  | some r =>
    let reads := r.program.filter fun n => match n.expression with | .readAt .. => true | _ => false
    let dispatch := r.program.filterMap fun n => match n.continuation with
      | .tagBind .isNullish yes no => some (yes, no)
      | _ => none
    match dispatch with
    | [(yes, no)] =>
      reads.length == 1 && yes.mapping == some [0, 2] && no.mapping == some [0, 2] &&
        reachesWrite r.program r.program.length yes.label &&
        !reachesWrite r.program r.program.length no.label
    | _ => false
  | none => false

/-! Claims no producer writes, on `identity(flag: boolean): boolean`: each
is refused, and evidence for the producer's claims justifies no other. -/

private def withFunction (name : String) (f : Json → Json) (claims : Json) : Json :=
  match claims.getObjValD "functions" with
  | .arr fs => claims.setObjVal! "functions" (.arr (fs.map fun g =>
      if g.getObjValD "name" == Json.str name then f g else g))
  | _ => claims
private def mapEach (key : String) (f : Json → Json) (j : Json) : Json :=
  match j.getObjValD key with
  | .arr xs => j.setObjVal! key (.arr (xs.map f))
  | _ => j
private def typed (labels : List Nat) (j : Json) : Json := j.setObjVal! "type" (toJson labels)
private def forged (f : Json → Json) : Json := withFunction "identity" f slotsClaims
/-- Refused, for the reason named. -/
private def refuses (r : Except String α) (reason : String) : Bool := match r with
  | .ok _ => false
  | .error e => (e.splitOn reason).length > 1

#guard ok (SourceClaimJson.produceJson slotsAst slotsClaims slotsFile 10)
-- The entry environment narrower than the parameter's annotation, alone or
-- with every claim inside the body narrowed with it: the edge from the
-- signature's inputs refuses it.
#guard refuses (SourceClaimJson.produceJson slotsAst
  (forged (mapEach "entries" (mapEach "bindings" (typed [2])))) slotsFile 10)
  "the edge from node 2 does not establish the claims at this point"
#guard refuses (SourceClaimJson.produceJson slotsAst
  (forged (fun f => mapEach "expressions" (typed [1])
    (mapEach "entries" (mapEach "bindings" (typed [1])) f))) slotsFile 10)
  "the edge from node 2 does not establish the claims at this point"
-- A parameter, result or expression claim other than the source's.
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (mapEach "params" (typed [2]))) slotsFile 10)
  "claimed parameter type differs from the source annotation for 'flag'"
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (·.setObjVal! "result" (toJson [2]))) slotsFile 10)
  "claimed return type differs from the source annotation"
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (mapEach "expressions" (typed [2]))) slotsFile 10)
  "no derivation of its node-typing claim"
-- A label outside the claims' type table, a missing environment, a binding
-- claimed twice.
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (mapEach "expressions" (typed [4]))) slotsFile 10)
  "no row 4"
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (·.setObjVal! "entries" (Json.arr #[]))) slotsFile 10)
  "missing statement environment at 432"
private def twice (e : Json) : Json := match e.getObjValD "bindings" with
  | .arr bs => e.setObjVal! "bindings" (.arr (bs ++ bs))
  | _ => e
#guard refuses (SourceClaimJson.produceJson slotsAst (forged (mapEach "entries" twice)) slotsFile 10)
  "duplicate identity, span, binding or type labels"

-- The evidence checks the claims it was produced for, and no other: a
-- certificate cannot be reused for a narrower environment or expression.
private def evidence : Json := (SourceClaimJson.produceJson slotsAst slotsClaims slotsFile 10).toOption.getD .null
#guard ok (SourceClaimJson.checkJson slotsAst slotsClaims slotsFile evidence)
#guard refuses (SourceClaimJson.checkJson slotsAst
  (forged (mapEach "entries" (mapEach "bindings" (typed [2])))) slotsFile evidence)
  "source evidence does not justify"
#guard refuses (SourceClaimJson.checkJson slotsAst (forged (mapEach "expressions" (typed [2]))) slotsFile evidence)
  "source evidence does not justify"

end Verification.Model.SourceExtractionTests
