// prettier-ignore
// Regression test: Class fields cannot have -readonly modifier
class Foo {
  // @skjs-expect-error 'a number' expected
  -readonly bar: string = "world"; }