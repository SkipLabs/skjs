/* @verify-report
 * Display-only claim report; not certificate input.
 * annotation-fields=kind,reason,id,unsupported
 * producer=skjs
 * source=verification/tests/programs/reject/inverted_narrowing.ts
 * source-sha256=732d3724f63c253b32c779bd1837dcca151120a7768f83b1b5c1fd8168500159
 * claimsSha256=5be2e0181af500e42409d2724683536d8ad906f1513cc233196503acf46eb2f7
 * diagnosticsSha256=7734dde2aaeb2589a3dc5867c0fa50bcdeb5b1238a7a1a502c971a19f4b985f2
 * Function results cover modeled obligations, not every exported claim.
 * Original spans are before annotation. Full details are in the companion JSON manifest.
 */
// SKJS must reject: the branch taken when `x === null` holds null, not string.
/* @verify-report kind=function; id=f0; function pick; producer=skjs; claimed (x: null | string) => string; verification=not-run; collection=aborted; quality=unverified; mode=normal */ function pick(x: string | null): string {
  /* @verify-report kind=entry; id=f0e0; unsupported=this; entry { this: (unavailable), x: null | string } @124:159 */ if (/* @verify-report kind=expression; id=f0x0; expr null | string @128:129 */ /* @verify-report kind=expression; id=f0x1; expr boolean @128:138 */ x === /* @verify-report kind=expression; id=f0x2; expr null @134:138 */ null) {
    /* @verify-report kind=entry; id=f0e1; unsupported=this; entry { this: (unavailable), x: null } @146:154 */ return /* @verify-report kind=expression; id=f0x3; expr null @153:154 */ x;
  }
  /* @verify-report kind=gap; reason=statement-not-visited; id=g0; statement not visited @162:177 */ return "other";
}
