type A = { kind: 'a'; next?: A } | B;
type B = { kind: 'b'; other?: B } | A;

function visit(node: A): string {
  if (node.kind === 'a') {
    return node.next ? visit(node.next) : 'done';
  }
  return node.other ? visit(node.other) : 'done';
}

const leaf: B = { kind: 'b' };
visit(leaf);
