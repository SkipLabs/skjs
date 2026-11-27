// prettier-ignore
// `import type "./foo.js"` is a syntax error in TypeScript (TS1005: '=' expected).
// @ts-expect-error 'a variable name' expected
import type "for-tests";
