// In a function type, a bare `(number)` is parsed as the parameter *name*,
// not its type. With no annotation it is reported as TS7006 — matching
// tsc's "Parameter 'number' implicitly has an 'any' type".

// @skjs-expect-error A parameter must have an explicit type annotation
type F1 = (number) => void;
