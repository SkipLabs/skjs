// Function type with a mix of annotated and unannotated parameters.
//
// The parser accepts an omitted parameter type; the checker then requires
// it, reporting the unannotated `y` as TS7006 — matching tsc's
// "Parameter 'y' implicitly has an 'any' type".
// @skjs-expect-error A parameter must have an explicit type annotation
type F = (x: number, y) => void;
