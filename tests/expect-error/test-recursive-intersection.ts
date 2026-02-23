// Recursive intersection types: ensure no infinite loops during expansion.

interface Wrap<T, U> {
  value: T;
  inner: Wrap<U, T>;
}

function testWrapInter(x: Wrap<string, number> & Wrap<number, string>): void {
  let y: Wrap<string, number> & Wrap<number, string> = x;
}

interface MyList<T> {
  head: T;
  tail: MyList<T> | null;
}

function testListInter(x: MyList<string> & MyList<string>): void {
  let y: MyList<string> = x;
}

interface TreeNode<T> {
  left: TreeNode<T> & TreeLeaf<T>;
  right: TreeNode<T>;
}
interface TreeLeaf<T> {
  value: T;
  parent: TreeNode<T> & TreeLeaf<T>;
}

function testTreeInter(x: TreeNode<string> & TreeLeaf<string>): void {
  let y: TreeNode<string> & TreeLeaf<string> = x;
  let v: string = x.value;
}
