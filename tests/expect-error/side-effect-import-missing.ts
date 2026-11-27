// Side-effect import of a missing module (currently rejected at parse time before resolution).
// @skjs-expect-error 'a variable name' expected
import "./nonexistent.js";
