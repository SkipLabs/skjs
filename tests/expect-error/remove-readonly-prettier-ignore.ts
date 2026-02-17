// Normal field
type Foo = {
  // @skjs-expect-error '-readonly' modifier can only appear in mapped types
  -readonly a: number;
};

// Index field
type Bar = {
  // @skjs-expect-error '-readonly' modifier can only appear in mapped types
  -readonly [k: string]: number;
};
