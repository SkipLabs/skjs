/* @verify-report
 * Display-only claim report; not certificate input.
 * annotation-fields=kind,reason,id,unsupported
 * producer=skjs
 * source=verification/tests/programs/accept/typeof_narrow.ts
 * source-sha256=42a67d3660232c894f6287187b98c6e4f82c61fe095973f567acd00fb021e342
 * claimsSha256=2e1d0f34ff808003521a9d46adb510cef824ed6128611e762b8faee786683c49
 * verifierSha256=553c194cb84ba688c0276d5154c6899a8b57aca0481fb9e0fb5bed71e2e314ab
 * parserSha256=561216e2553dc46fe72edc8ef994d9f4f83dc843aefcd318ce57fc6a9a733556
 * Function results cover modeled obligations, not every exported claim.
 * Original spans are before annotation. Full details are in the companion JSON manifest.
 */
/* @verify-report kind=function; id=f0; function describe; producer=skjs; claimed (x: null | number | string) => string; verification=not-established; collection=complete; quality=unverified; mode=normal; reject: expression outside the stateful source slice */ function describe(x: string | number | null): string {
  /* @verify-report kind=entry; id=f0e0; unsupported=this; entry { this: (unavailable), x: null | number | string } @57:103 */ if (/* @verify-report kind=expression; id=f0x0; expr string @61:69 */ /* @verify-report kind=expression; id=f0x1; expr boolean @61:82 */ typeof /* @verify-report kind=expression; id=f0x2; expr null | number | string @68:69 */ x === /* @verify-report kind=expression; id=f0x3; expr "string" @74:82 */ "string") {
    /* @verify-report kind=entry; id=f0e1; unsupported=this; entry { this: (unavailable), x: string } @90:98 */ return /* @verify-report kind=expression; id=f0x4; expr string @97:98 */ x;
  }
  /* @verify-report kind=entry; id=f0e2; unsupported=this; entry { this: (unavailable), x: null | number } @106:161 */ if (/* @verify-report kind=expression; id=f0x5; expr string @110:118 */ /* @verify-report kind=expression; id=f0x6; expr boolean @110:131 */ typeof /* @verify-report kind=expression; id=f0x7; expr null | number @117:118 */ x === /* @verify-report kind=expression; id=f0x8; expr "number" @123:131 */ "number") {
    /* @verify-report kind=entry; id=f0e3; unsupported=this; entry { this: (unavailable), x: number } @139:156 */ return /* @verify-report kind=expression; id=f0x9; expr "a number" @146:156 */ "a number";
  }
  /* @verify-report kind=entry; id=f0e4; unsupported=this; entry { this: (unavailable), x: null } @164:177 */ return /* @verify-report kind=expression; id=f0x10; expr "null" @171:177 */ "null";
}
