// @skjs-expect-error Invalid import: local imports must be from js files
import { x } from "./nonexistent";

import { y } from "nonexistent";
