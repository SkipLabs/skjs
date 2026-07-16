// A genuine cycle that spans two files: `Alpha` resolves to `Beta`, which
// resolves back to `Alpha`. Both are circular, and — like tsc — both are
// reported, each at its own declaration.
import { Beta } from "./beta";

// @skjs-expect-error Type alias 'Alpha' circularly references itself
export type Alpha = Beta;
