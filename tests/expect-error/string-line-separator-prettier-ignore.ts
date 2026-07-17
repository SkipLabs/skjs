// A <LS> (U+2028) is legal inside a string literal -- ES2019 admits it, unlike
// <LF>/<CR> -- and it still ends a line, so the error below is on line 5 rather
// than line 4. That is only visible if the annotation harness counts the same
// line terminators the compiler does; it keeps its own counter on purpose, to
// double-check the compiler's, so the two have to agree independently.
//
// The <LS> is a real byte: the file is prettier-exempt and marked -text.
function f(): void {
  const s = "a b";
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const y: number = "x";
  console.log(s, y);
}
