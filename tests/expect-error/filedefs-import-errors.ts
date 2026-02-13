// @skjs-expect-error Relative imports require a '.js', '.mjs', or '.cjs' extension. Use 'moduleResolution: "bundler"' for extensionless imports
// @skjs-expect-error Could not find module './nonexistent'
import { x } from "./nonexistent";

// @skjs-expect-error Could not find module 'nonexistent'
import { y } from "nonexistent";
