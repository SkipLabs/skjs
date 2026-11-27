// Side-effect import of a missing module resolves the specifier and reports TS2307.
// @ts-expect-error Cannot find module './nonexistent.js' or its corresponding type declarations
import "./nonexistent.js";
