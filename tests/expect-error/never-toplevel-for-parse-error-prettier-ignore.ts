declare function f4(): never;

// A top-level `for` statement is a parse error in SKJS (parse errors must be
// the last non-empty line of the file).
// @skjs-expect-error ')' or ',' expected
for (const n of f4()) {}
