// @skjs-expect-error Construction not supported: export default (ignored)
export default 42;

// @skjs-expect-error Construction not supported: export as (ignored)
export as namespace MyLib;

// @skjs-expect-error Construction not supported: export = (ignored)
export = 42;
