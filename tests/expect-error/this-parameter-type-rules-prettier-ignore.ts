// Test this parameter rules in function types

// this parameter cannot be optional in function types
// @skjs-expect-error this cannot be optional
type FuncWithOptionalThis = (this?: string) => void;

// this parameter cannot be a spread parameter in function types
// @skjs-expect-error this cannot be a spread parameter
type FuncWithSpreadThis = (...this: string[]) => void;
