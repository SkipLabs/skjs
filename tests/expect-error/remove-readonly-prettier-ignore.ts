// Normal field
type Foo = {
  // @skjs-expect-error '-readonly' modifier can only appear in a mapped type
  -readonly a: number;
};

// Index field
type Bar = {
  // @skjs-expect-error '-readonly' modifier can only appear in a mapped type
  -readonly [k: string]: number;
};
