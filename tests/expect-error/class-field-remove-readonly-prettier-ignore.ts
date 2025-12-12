// prettier-ignore
// Regression test: Class fields cannot have -readonly modifier
class Foo {
  // @ts-expect-error Expected token a number
  -readonly bar: string = "world"; }