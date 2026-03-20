// Tests that subtypingEdges from failed branch-level subtyping checks
// are rolled back. When Obj <: (BranchA | BranchB) is checked,
// TObject::isSub tries each branch. Matching BranchA: method 'a'
// succeeds (Obj.a <: BranchA.a, recording subtypingEdge) but field
// 'b' fails (number vs string), so subst is restored and BranchB is
// tried instead. Without save/restore for subtypingEdges, the edge
// from the failed BranchA attempt persists as a spurious dependency.
//
// SPURIOUS: method:Obj.a reaches fn:useBranchA through the spurious
// subtypingEdge method:Obj.a → method:BranchA.a from the failed
// BranchA check.

interface BranchA {
  a(x: number): void;
  b: string;
}

interface BranchB {
  a(x: number): void;
  b: number;
}

class Obj {
  a(x: number): void {}
  b: number = 0;
}

function useBranchA(t: BranchA): void {
  t.a(1);
}

function useMixed(t: BranchA | BranchB): void {}

// @skjs-callgraph-closure
// method:Obj.a: fn:useBranchA
function test(): void {
  const obj = new Obj();
  useMixed(obj);
}
