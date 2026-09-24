import { get } from "./dep.js";
import type { Box } from "./dep.js";
import type { RemoteBox } from "./reexport.js";

// Two different mention names still denote the same declaration.
function reexportedIdentity(b: RemoteBox): Box {
  return b;
}

function reexportedArgument(b: RemoteBox): string {
  return get(b);
}
