// @skjs-expect-error This export form is not yet supported by SKJS
// @skjs-expect-error export default is not supported by SKJS (ignored)
export default 42;

// @skjs-expect-error This export form is not yet supported by SKJS
// @skjs-expect-error export as is not supported by SKJS (ignored)
export as namespace MyLib;

// @skjs-expect-error This export form is not yet supported by SKJS
// @skjs-expect-error export = is not supported by SKJS (ignored)
export = 42;
