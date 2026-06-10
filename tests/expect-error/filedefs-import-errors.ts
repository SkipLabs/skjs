// @skjs-expect-error Relative imports require a '.js', '.mjs', or '.cjs' extension. Use 'moduleResolution: "bundler"' for extensionless imports.
// @skjs-expect-error Cannot find module './nonexistent' or its corresponding type declarations
import { x } from "./nonexistent";

// @skjs-expect-error Cannot find module 'nonexistent' or its corresponding type declarations
import { y } from "nonexistent";
