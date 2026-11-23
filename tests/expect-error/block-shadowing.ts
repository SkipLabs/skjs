// Nested block shadowing: an inner block may reuse a name bound in an
// enclosing block (`const x = 1; { const x = 2; }`), the way tsc allows.
// Only a redeclaration within the same scope — including a function body's
// top level against its own parameters — is an error.

const moduleLevel: number = 1;

function shadowsModuleLevel(): void {
  const moduleLevel = 2;
  __SKJS_show_expanded(moduleLevel, "2");
}

function nestedConstBlock(): void {
  const x = 1;
  {
    const x = "s";
    __SKJS_show_expanded(x, '"s"');
  }
  __SKJS_show_expanded(x, "1");
}

function nestedLetBlock(): void {
  let x = 1;
  {
    let x = "s";
    __SKJS_show_expanded(x, "string");
  }
  __SKJS_show_expanded(x, "number");
}

function siblingBlocks(): void {
  const x = 1;
  {
    const x = 2;
  }
  {
    const x = 3;
  }
}

function multiLevelNesting(): void {
  const x = 1;
  {
    const x = "a";
    {
      const x = true;
      __SKJS_show_expanded(x, "true");
    }
    __SKJS_show_expanded(x, '"a"');
  }
  __SKJS_show_expanded(x, "1");
}

function ifBlockShadows(): void {
  const x = 1;
  if (x === 1) {
    const x = 2;
  }
}

function elseBlockShadows(): void {
  const x = 1;
  if (x !== 1) {
    const x = 2;
  } else {
    const x = 3;
  }
}

function whileBlockShadows(): void {
  let x = 1;
  while (x < 2) {
    const x = 3;
  }
}

function forBodyShadows(): void {
  for (let i = 0; i < 1; i++) {
    const i = 2;
  }
}

function forOfBodyShadows(): void {
  for (const k of ["a"]) {
    const k = "b";
  }
}

function tryBlockShadows(): void {
  const x = 1;
  try {
    const x = 2;
  } catch (e) {
    const x = 3;
  } finally {
    const x = 4;
  }
}

function catchBlockShadows(): void {
  const x = 1;
  try {
    const y = 1;
  } catch (e) {
    const x = 3;
  }
}

function switchCaseBlockShadows(v: number): void {
  const x = 1;
  switch (v) {
    case 1: {
      const x = 2;
      break;
    }
    default: {
      const x = 3;
      break;
    }
  }
}

function paramVsNestedBlock(x: number): void {
  {
    const x = "s";
    __SKJS_show_expanded(x, '"s"');
  }
  __SKJS_show_expanded(x, "number");
}

function catchParamVsNestedBlock(): void {
  try {
    const y = 1;
  } catch (e) {
    {
      const e = 1;
    }
  }
}

function lambdaShadowsOuterLocal(): void {
  const x = 1;
  const f = (): number => {
    const x = 2;
    return x;
  };
}

function destructuringShadows(): void {
  const p = 1;
  {
    const { p } = { p: 2 };
    __SKJS_show_expanded(p, "2");
  }
  __SKJS_show_expanded(p, "1");
}

function innerBlockWritesOuterBinding(): void {
  let x: number | string = 1;
  {
    x = "s";
  }
  __SKJS_show_expanded(x, "number | string");
}

function blockLocalNotVisibleAfter(): void {
  {
    const y = 2;
  }
  // @skjs-expect-error Cannot find name
  const z = y;
}

function sameBlockRedeclare(): void {
  const x = 1;
  // @ts-expect-error Cannot redeclare block-scoped variable 'x'
  const x = 2;
}

function sameBlockMixedKinds(): void {
  let x = 1;
  // @ts-expect-error Cannot redeclare block-scoped variable 'x'
  const x = 2;
}

function sameDeclarationList(): void {
  const x = 1,
    // @ts-expect-error Cannot redeclare block-scoped variable 'x'
    x = 2;
}

function paramVsBody(x: number): void {
  // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
  const x = 1;
}

function arrowParamVsBody(): void {
  const f = (x: number): number => {
    // @skjs-expect-error Cannot redeclare block-scoped variable 'x'
    const x = 1;
    return x;
  };
}

function catchParamVsBody(): void {
  try {
    const y = 1;
  } catch (e) {
    // @skjs-expect-error Cannot redeclare block-scoped variable 'e'
    const e = 1;
  }
}

function switchCasesShareScope(v: number): void {
  switch (v) {
    case 1:
      const x = 1;
      break;
    case 2:
      // @ts-expect-error Cannot redeclare block-scoped variable 'x'
      const x = 2;
      break;
  }
}

function forHeadDeclarationList(): void {
  // @ts-expect-error Cannot redeclare block-scoped variable 'i'
  for (let i = 0, i = 1; i < 2; i++) {
    const j = i;
  }
}

// Jump-edge snapshots are keyed by binding identity, not bare name
// (SkipLabs/skjs#1018, activated by #1090): a `break` recorded from inside a
// clause block that shadows `x` must still carry the outer `x`'s write from
// earlier in the clause. With name-keyed snapshots the shadowing entry won
// the snapshot entry and the below-baseline drop removed it whole, so the
// outer binding's edge value was lost and `x` read as `number` only after the
// switch — unsound.
function switchBreakEdgeKeepsOuterWrite(v: number, cond: boolean): void {
  let x: number | string = 0;
  switch (v) {
    case 1:
      if (cond) {
        x = "s";
        {
          const x = true;
          break;
        }
      }
      break;
    default:
      break;
  }
  __SKJS_show_expanded(x, "number | string");
}
