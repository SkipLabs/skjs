// @skjs-callgraph-full
// fn:outer: lambda:function(outer)@32
// fn:withNested: lambda:function(withNested)@36
// lambda:function(withNested)@36: lambda:function(withNested)@75

function outer(): number {
  const fn = (x: number): number => x + 1;
  return fn(1);
}

function withNested(): number {
  const f = (x: number): number => {
    const g = (y: number): number => y;
    return g(x);
  };
  return f(1);
}
