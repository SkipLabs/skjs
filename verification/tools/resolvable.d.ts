// The verifier's own declaration a program writes to qualify a type
// parameter: `T extends Resolvable` makes `T` resolution-qualified, owning its
// observation and result (SOURCE-CONTRACTS.md, "Implied bounds"). The parser
// recognizes the bound by this declaration, which TypeScript binds the name
// to, never by its spelling. As a type it is `unknown`: the qualification
// constrains which instances a call may take, not the values of `T`.
type Resolvable = unknown;
