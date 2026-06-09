// @skjs-expect-error Construction not supported: export default (ignored)
// @skjs-expect-error This export form is not yet supported by SKJS
export default 42;

// @skjs-expect-error Construction not supported: export as (ignored)
// @skjs-expect-error This export form is not yet supported by SKJS
export as namespace MyLib;

// @skjs-expect-error Construction not supported: export = (ignored)
// @skjs-expect-error This export form is not yet supported by SKJS
export = 42;
