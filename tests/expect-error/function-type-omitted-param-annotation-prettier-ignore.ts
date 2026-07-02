// Function type with a mix of annotated and unannotated parameters.
//
// Today the omitted annotation on `y` is a parse error. Once the parser
// permits an omitted parameter type (TAFunParam.type is optional), this
// will instead report TS7006 on `y` (SKJS: "A parameter must have an
// explicit type annotation"; tsc: "Parameter 'y' implicitly has an 'any'
// type"), flipping the annotation below and dropping the -prettier-ignore
// suffix.
// @skjs-expect-error ':' expected
type F = (x: number, y) => void;
