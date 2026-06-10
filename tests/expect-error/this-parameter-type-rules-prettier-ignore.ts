// Test this parameter rules in function types

// this parameter cannot be optional in function types
// @skjs-expect-error A 'this' parameter cannot be optional
type FuncWithOptionalThis = (this?: string) => void;

// this parameter cannot be a rest parameter in function types
// @skjs-expect-error A 'this' parameter cannot be a rest parameter
type FuncWithSpreadThis = (...this: string[]) => void;

// this parameter cannot have a default value in a function definition
declare const defaultCtx: { value: number };
// @skjs-expect-error A 'this' parameter cannot have a default value
function withThisDefault(this: { value: number } = defaultCtx): void {}
