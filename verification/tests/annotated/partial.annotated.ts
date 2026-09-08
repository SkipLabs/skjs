/* @verify-report
 * Display-only claim report; not certificate input.
 * annotation-fields=kind,reason,id,unsupported
 * producer=skjs
 * source=verification/tests/partial-claims.ts
 * source-sha256=e1b9623b2fb32ebc86da6e03b51666048b4eb21fc83dfc40f7792b2800f6a5df
 * claimsSha256=9e7ddeba36dbb2cf76d3fb1af93ac72a6fe64be96caa3cc06bc1bce9fb9f3e98
 * verifierSha256=b2d2b3e50816f832570eff0e4c699d11ccb944acd9ac6dbeba4de656b2cd622a
 * parserSha256=0eed1ca4aaf10e2be524941307992fb7c07a3d5481f5c1d46f2397fa552de98d
 * diagnosticsSha256=a5bd9fd66e9c32f26791eaf07ed015116339b81a8a20c04a9c9e8cbe239e1c3d
 * Function results cover modeled obligations, not every exported claim.
 * Original spans are before annotation. Full details are in the companion JSON manifest.
 */
// Deliberately rejected: ordinary checking must retain the prefix without recovery.
/* @verify-report kind=function; id=f0; function annotationFailure; producer=skjs; claimed () => boolean; verification=not-established; collection=aborted; quality=unverified; mode=normal; reject: source environment obligation at 186: missing statement environment at 186 */ function annotationFailure(): boolean {
  /* @verify-report kind=entry; id=f0e0; unsupported=this; entry { this: (unavailable) } @127:155 */ const before: boolean = /* @verify-report kind=expression; id=f0x0; expr true @151:155 */ true;
  /* @verify-report kind=entry; id=f0e1; unsupported=this; entry { before: boolean, this: (unavailable) } @159:182 */ const bad: true = /* @verify-report kind=expression; id=f0x1; expr false @177:182 */ false;
  /* @verify-report kind=gap; reason=statement-not-visited; id=g0; statement not visited @186:214 */ const after: boolean = true;
  /* @verify-report kind=gap; reason=statement-not-visited; id=g1; statement not visited @217:230 */ return after;
}

/* @verify-report kind=function; id=f2; function expressionFailure; producer=skjs; claimed () => boolean; verification=not-established; collection=aborted; quality=unverified; mode=normal; reject: no claimed type for the expression at [329,336) */ function expressionFailure(): boolean {
  /* @verify-report kind=entry; id=f2e0; unsupported=this; entry { this: (unavailable) } @276:304 */ const before: boolean = /* @verify-report kind=expression; id=f2x0; expr true @300:304 */ true;
  /* @verify-report kind=entry; id=f2e1; unsupported=this; entry { before: boolean, this: (unavailable) } @308:336 */ const bad: boolean = /* @verify-report kind=gap; reason=expression-without-type; id=g2; expression entered without a type result @329:336 */ missing;
  /* @verify-report kind=gap; reason=statement-not-visited; id=g3; statement not visited @340:354 */ return before;
}

/* @verify-report kind=function; id=f1; function complete; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function complete(): boolean {
  /* @verify-report kind=entry; id=f1e0; unsupported=this; entry { this: (unavailable) } @391:402 */ return /* @verify-report kind=expression; id=f1x0; expr true @398:402 */ true;
}
