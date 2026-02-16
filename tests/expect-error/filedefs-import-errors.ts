// @skjs-expect-error Invalid import: local imports must be from js files
// @skjs-expect-error Could not find module './nonexistent'
import { x } from "./nonexistent";

// @skjs-expect-error Could not find module 'nonexistent'
import { y } from "nonexistent";
