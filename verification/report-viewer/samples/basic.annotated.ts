/* @verify-report
 * Display-only claim report; not certificate input.
 * annotation-fields=kind,reason,id,unsupported
 * producer=skjs
 * source=verification/tests/stateful-source/basic.ts
 * source-sha256=ed941574a4ac573d93a978ee4273a57fe449be5501a9d1c91bda1d26a249b749
 * claimsSha256=26f013cf9254fd361b5edaab19fbde5ce6a528bb456fd61b22bc3b560c73350e
 * verifierSha256=b2d2b3e50816f832570eff0e4c699d11ccb944acd9ac6dbeba4de656b2cd622a
 * parserSha256=0eed1ca4aaf10e2be524941307992fb7c07a3d5481f5c1d46f2397fa552de98d
 * Function results cover modeled obligations, not every exported claim.
 * Original spans are before annotation. Full details are in the companion JSON manifest.
 */
/* @verify-report kind=function; id=f9; function copyTrue; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function copyTrue(): boolean {
  /* @verify-report kind=entry; id=f9e0; unsupported=this; entry { this: (unavailable) } @33:53 */ const x: true = /* @verify-report kind=expression; id=f9x0; expr true @49:53 */ true;
  /* @verify-report kind=entry; id=f9e1; unsupported=this; entry { this: (unavailable), x: true } @57:77 */ const y: boolean = /* @verify-report kind=expression; id=f9x1; expr true @76:77 */ x;
  /* @verify-report kind=entry; id=f9e2; unsupported=this; entry { this: (unavailable), x: true, y: boolean } @81:89 */ return /* @verify-report kind=expression; id=f9x2; expr boolean @88:89 */ y;
}

/* @verify-report kind=function; id=f7; function copyFalse; producer=skjs; claimed () => false; verification=verified; collection=complete; quality=unverified; mode=normal */ function copyFalse(): false {
  /* @verify-report kind=entry; id=f7e0; unsupported=this; entry { this: (unavailable) } @126:141 */ const x = /* @verify-report kind=expression; id=f7x0; expr false @136:141 */ false;
  /* @verify-report kind=entry; id=f7e1; unsupported=this; entry { this: (unavailable), x: false } @145:153 */ return /* @verify-report kind=expression; id=f7x1; expr false @152:153 */ x;
}

/* @verify-report kind=function; id=f4; function nullOrBoolean; producer=skjs; claimed () => boolean | null; verification=verified; collection=complete; quality=unverified; mode=normal */ function nullOrBoolean(): null | boolean {
  /* @verify-report kind=entry; id=f4e0; unsupported=this; entry { this: (unavailable) } @203:233 */ const x: null | boolean = /* @verify-report kind=expression; id=f4x0; expr null @229:233 */ null;
  /* @verify-report kind=entry; id=f4e1; unsupported=this; entry { this: (unavailable), x: boolean | null } @237:245 */ return /* @verify-report kind=expression; id=f4x1; expr boolean | null @244:245 */ x;
}

/* @verify-report kind=function; id=f0; function keepOlderBinding; producer=skjs; claimed () => true; verification=verified; collection=complete; quality=unverified; mode=normal */ function keepOlderBinding(): true {
  /* @verify-report kind=entry; id=f0e0; unsupported=this; entry { this: (unavailable) } @288:308 */ const x: true = /* @verify-report kind=expression; id=f0x0; expr true @304:308 */ true;
  /* @verify-report kind=entry; id=f0e1; unsupported=this; entry { this: (unavailable), x: true } @312:334 */ const y: false = /* @verify-report kind=expression; id=f0x1; expr false @329:334 */ false;
  /* @verify-report kind=entry; id=f0e2; unsupported=this; entry { this: (unavailable), x: true, y: false } @338:346 */ return /* @verify-report kind=expression; id=f0x2; expr true @345:346 */ x;
}

/* @verify-report kind=function; id=f12; function mergeWithLocals; producer=skjs; claimed () => true; verification=verified; collection=complete; quality=unverified; mode=normal */ function mergeWithLocals(): true {
  /* @verify-report kind=entry; id=f12e0; unsupported=this; entry { this: (unavailable) } @388:412 */ const outer: true = /* @verify-report kind=expression; id=f12x0; expr true @408:412 */ true;
  /* @verify-report kind=entry; id=f12e1; unsupported=this; entry { outer: true, this: (unavailable) } @416:536 */ if (/* @verify-report kind=expression; id=f12x1; expr true @420:424 */ true) {
    /* @verify-report kind=entry; id=f12e2; unsupported=this; entry { outer: true, this: (unavailable) } @432:458 */ const local: false = /* @verify-report kind=expression; id=f12x2; expr false @453:458 */ false;
    /* @verify-report kind=entry; id=f12e3; unsupported=this; entry { local: false, outer: true, this: (unavailable) } @464:490 */ const another: null = /* @verify-report kind=expression; id=f12x3; expr null @486:490 */ null;
  } else {
    /* @verify-report kind=entry; id=f12e4; unsupported=this; entry { outer: true, this: (unavailable) } @507:531 */ const local: null = /* @verify-report kind=expression; id=f12x4; expr null @527:531 */ null;
  }
  /* @verify-report kind=entry; id=f12e5; unsupported=this; entry { outer: true, this: (unavailable) } @539:551 */ return /* @verify-report kind=expression; id=f12x5; expr true @546:551 */ outer;
}

/* @verify-report kind=function; id=f10; function bothReturn; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function bothReturn(): boolean {
  /* @verify-report kind=entry; id=f10e0; unsupported=this; entry { this: (unavailable) } @591:653 */ if (/* @verify-report kind=expression; id=f10x0; expr false @595:600 */ false) {
    /* @verify-report kind=entry; id=f10e1; unsupported=this; entry { this: (unavailable) } @608:619 */ return /* @verify-report kind=expression; id=f10x1; expr true @615:619 */ true;
  } else {
    /* @verify-report kind=entry; id=f10e2; unsupported=this; entry { this: (unavailable) } @636:648 */ return /* @verify-report kind=expression; id=f10x2; expr false @643:648 */ false;
  }
}

/* @verify-report kind=function; id=f11; function nestedMerge; producer=skjs; claimed () => null; verification=verified; collection=complete; quality=unverified; mode=normal */ function nestedMerge(): null {
  /* @verify-report kind=entry; id=f11e0; unsupported=this; entry { this: (unavailable) } @690:714 */ const outer: null = /* @verify-report kind=expression; id=f11x0; expr null @710:714 */ null;
  /* @verify-report kind=entry; id=f11e1; unsupported=this; entry { outer: null, this: (unavailable) } @718:822 */ if (/* @verify-report kind=expression; id=f11x1; expr true @722:726 */ true) {
    /* @verify-report kind=entry; id=f11e2; unsupported=this; entry { outer: null, this: (unavailable) } @734:762 */ const local: boolean = /* @verify-report kind=expression; id=f11x2; expr false @757:762 */ false;
    /* @verify-report kind=entry; id=f11e3; unsupported=this; entry { local: boolean, outer: null, this: (unavailable) } @768:818 */ if (/* @verify-report kind=expression; id=f11x3; expr false @772:777 */ false) {
      /* @verify-report kind=entry; id=f11e4; unsupported=this; entry { local: boolean, outer: null, this: (unavailable) } @787:811 */ const inner: true = /* @verify-report kind=expression; id=f11x4; expr true @807:811 */ true;
    }
  }
  /* @verify-report kind=entry; id=f11e5; unsupported=this; entry { outer: null, this: (unavailable) } @825:837 */ return /* @verify-report kind=expression; id=f11x5; expr null @832:837 */ outer;
}

/* @verify-report kind=function; id=f14; function earlyArm; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function earlyArm(): boolean {
  /* @verify-report kind=entry; id=f14e0; unsupported=this; entry { this: (unavailable) } @875:901 */ const outer: false = /* @verify-report kind=expression; id=f14x0; expr false @896:901 */ false;
  /* @verify-report kind=entry; id=f14e1; unsupported=this; entry { outer: false, this: (unavailable) } @905:938 */ if (/* @verify-report kind=expression; id=f14x1; expr false @909:914 */ false) {
    /* @verify-report kind=entry; id=f14e2; unsupported=this; entry { outer: false, this: (unavailable) } @922:933 */ return /* @verify-report kind=expression; id=f14x2; expr true @929:933 */ true;
  }
  /* @verify-report kind=entry; id=f14e3; unsupported=this; entry { outer: false, this: (unavailable) } @941:953 */ return /* @verify-report kind=expression; id=f14x3; expr false @948:953 */ outer;
}

/* @verify-report kind=function; id=f2; function narrowVariable; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function narrowVariable(): boolean {
  /* @verify-report kind=entry; id=f2e0; unsupported=this; entry { this: (unavailable) } @997:1028 */ const condition: boolean = /* @verify-report kind=expression; id=f2x0; expr true @1024:1028 */ true;
  /* @verify-report kind=entry; id=f2e1; unsupported=this; entry { condition: boolean, this: (unavailable) } @1032:1060 */ const other: boolean = /* @verify-report kind=expression; id=f2x1; expr false @1055:1060 */ false;
  /* @verify-report kind=entry; id=f2e2; unsupported=this; entry { condition: boolean, other: boolean, this: (unavailable) } @1064:1192 */ if (/* @verify-report kind=expression; id=f2x2; expr boolean @1068:1077 */ condition) {
    /* @verify-report kind=entry; id=f2e3; unsupported=this; entry { condition: true, other: boolean, this: (unavailable) } @1085:1112 */ const yes: true = /* @verify-report kind=expression; id=f2x3; expr true @1103:1112 */ condition;
    /* @verify-report kind=entry; id=f2e4; unsupported=this; entry { condition: true, other: boolean, this: (unavailable), yes: true } @1118:1128 */ return /* @verify-report kind=expression; id=f2x4; expr true @1125:1128 */ yes;
  } else {
    /* @verify-report kind=entry; id=f2e5; unsupported=this; entry { condition: false, other: boolean, this: (unavailable) } @1145:1172 */ const no: false = /* @verify-report kind=expression; id=f2x5; expr false @1163:1172 */ condition;
    /* @verify-report kind=entry; id=f2e6; unsupported=this; entry { condition: false, no: false, other: boolean, this: (unavailable) } @1178:1187 */ return /* @verify-report kind=expression; id=f2x6; expr false @1185:1187 */ no;
  }
}

/* @verify-report kind=function; id=f1; function refineThenMerge; producer=skjs; claimed () => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function refineThenMerge(): boolean {
  /* @verify-report kind=entry; id=f1e0; unsupported=this; entry { this: (unavailable) } @1236:1268 */ const condition: boolean = /* @verify-report kind=expression; id=f1x0; expr false @1263:1268 */ false;
  /* @verify-report kind=entry; id=f1e1; unsupported=this; entry { condition: boolean, this: (unavailable) } @1272:1369 */ if (/* @verify-report kind=expression; id=f1x1; expr boolean @1276:1285 */ condition) {
    /* @verify-report kind=entry; id=f1e2; unsupported=this; entry { condition: true, this: (unavailable) } @1293:1320 */ const yes: true = /* @verify-report kind=expression; id=f1x2; expr true @1311:1320 */ condition;
  } else {
    /* @verify-report kind=entry; id=f1e3; unsupported=this; entry { condition: false, this: (unavailable) } @1337:1364 */ const no: false = /* @verify-report kind=expression; id=f1x3; expr false @1355:1364 */ condition;
  }
  /* @verify-report kind=entry; id=f1e4; unsupported=this; entry { condition: boolean, this: (unavailable) } @1372:1388 */ return /* @verify-report kind=expression; id=f1x4; expr boolean @1379:1388 */ condition;
}

/* @verify-report kind=function; id=f3; function selectParameter; producer=skjs; claimed (first: null, second: boolean) => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function selectParameter(first: null, second: boolean): boolean {
  /* @verify-report kind=entry; id=f3e0; unsupported=this; entry { first: null, second: boolean, this: (unavailable) } @1461:1489 */ const copy: boolean = /* @verify-report kind=expression; id=f3x0; expr boolean @1483:1489 */ second;
  /* @verify-report kind=entry; id=f3e1; unsupported=this; entry { copy: boolean, first: null, second: boolean, this: (unavailable) } @1493:1504 */ return /* @verify-report kind=expression; id=f3x1; expr boolean @1500:1504 */ copy;
}

/* @verify-report kind=function; id=f5; function narrowParameter; producer=skjs; claimed (condition: boolean, value: null) => boolean; verification=verified; collection=complete; quality=unverified; mode=normal */ function narrowParameter(condition: boolean, value: null): boolean {
  /* @verify-report kind=entry; id=f5e0; unsupported=this; entry { condition: boolean, this: (unavailable), value: null } @1580:1682 */ if (/* @verify-report kind=expression; id=f5x0; expr boolean @1584:1593 */ condition) {
    /* @verify-report kind=entry; id=f5e1; unsupported=this; entry { condition: true, this: (unavailable), value: null } @1601:1628 */ const yes: true = /* @verify-report kind=expression; id=f5x1; expr true @1619:1628 */ condition;
    /* @verify-report kind=entry; id=f5e2; unsupported=this; entry { condition: true, this: (unavailable), value: null, yes: true } @1634:1644 */ return /* @verify-report kind=expression; id=f5x2; expr true @1641:1644 */ yes;
  } else {
    /* @verify-report kind=entry; id=f5e3; unsupported=this; entry { condition: false, this: (unavailable), value: null } @1661:1677 */ return /* @verify-report kind=expression; id=f5x3; expr false @1668:1677 */ condition;
  }
}

/* @verify-report kind=function; id=f6; function parameterMerge; producer=skjs; claimed (condition: boolean, value: null) => null; verification=verified; collection=complete; quality=unverified; mode=normal */ function parameterMerge(condition: boolean, value: null): null {
  /* @verify-report kind=entry; id=f6e0; unsupported=this; entry { condition: boolean, this: (unavailable), value: null } @1753:1850 */ if (/* @verify-report kind=expression; id=f6x0; expr boolean @1757:1766 */ condition) {
    /* @verify-report kind=entry; id=f6e1; unsupported=this; entry { condition: true, this: (unavailable), value: null } @1774:1801 */ const yes: true = /* @verify-report kind=expression; id=f6x1; expr true @1792:1801 */ condition;
  } else {
    /* @verify-report kind=entry; id=f6e2; unsupported=this; entry { condition: false, this: (unavailable), value: null } @1818:1845 */ const no: false = /* @verify-report kind=expression; id=f6x2; expr false @1836:1845 */ condition;
  }
  /* @verify-report kind=entry; id=f6e3; unsupported=this; entry { condition: boolean, this: (unavailable), value: null } @1853:1865 */ return /* @verify-report kind=expression; id=f6x3; expr null @1860:1865 */ value;
}

/* @verify-report kind=function; id=f8; function singletonParameter; producer=skjs; claimed (exact: true) => true; verification=verified; collection=complete; quality=unverified; mode=normal */ function singletonParameter(exact: true): true {
  /* @verify-report kind=entry; id=f8e0; unsupported=this; entry { exact: true, this: (unavailable) } @1921:1933 */ return /* @verify-report kind=expression; id=f8x0; expr true @1928:1933 */ exact;
}

/* @verify-report kind=function; id=f13; function unionParameter; producer=skjs; claimed (value: boolean | null) => boolean | null; verification=verified; collection=complete; quality=unverified; mode=normal */ function unionParameter(value: null | boolean): null | boolean {
  /* @verify-report kind=entry; id=f13e0; unsupported=this; entry { this: (unavailable), value: boolean | null } @2005:2017 */ return /* @verify-report kind=expression; id=f13x0; expr boolean | null @2012:2017 */ value;
}
