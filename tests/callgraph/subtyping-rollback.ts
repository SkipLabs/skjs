// Tests that subtypingEdges from failed branch-level subtyping checks
// are rolled back. When Obj <: (BranchA | BranchB) is checked,
// TObject::isSub tries each branch. Matching BranchA: method 'a'
// succeeds (Obj.a <: BranchA.a, recording subtypingEdge) but field
// 'b' fails (number vs string), so subst is restored and BranchB is
// tried instead. The subtypingEdge from the failed BranchA attempt
// is rolled back along with the rest of the subst state.
//
// method:Obj.a should NOT reach fn:useBranchA — it only reaches
// method:BranchB.a (the matching branch).

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
// method:Obj.a: method:BranchB.a
function test(): void {
  const obj = new Obj();
  useMixed(obj);
}
