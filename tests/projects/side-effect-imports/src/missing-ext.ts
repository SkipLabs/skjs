// Extensionless relative side-effect import under node16 reports the extension rule.
// @skjs-expect-error Relative imports require a '.js', '.mjs', or '.cjs' extension. Use 'moduleResolution: "bundler"' for extensionless imports.
import "./side-effect";
