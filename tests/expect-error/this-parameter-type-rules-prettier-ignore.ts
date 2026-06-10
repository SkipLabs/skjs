// Test this parameter rules in function types

// this parameter cannot be optional in function types
// @skjs-expect-error A 'this' parameter cannot be optional
type FuncWithOptionalThis = (this?: string) => void;

// this parameter cannot be a rest parameter in function types
// @skjs-expect-error A 'this' parameter cannot be a rest parameter
type FuncWithSpreadThis = (...this: string[]) => void;
