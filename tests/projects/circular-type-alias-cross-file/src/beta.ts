import { Alpha } from "./alpha";

// @skjs-expect-error Type alias 'Beta' circularly references itself
export type Beta = Alpha;
