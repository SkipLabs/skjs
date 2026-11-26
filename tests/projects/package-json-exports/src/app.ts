// Currently before #611, `exports` is ignored:
// - "dual-pkg" falls back to `types: "./legacy.d.ts"` (so mainEntry is missing)
// - subpath imports fail with TS2307
import { mainEntry } from "dual-pkg";
// @skjs-expect-error Cannot find module 'dual-pkg/utils' or its corresponding type declarations
import { utilFn } from "dual-pkg/utils";
// @skjs-expect-error Cannot find module 'dual-pkg/sub/helper' or its corresponding type declarations
import { helper } from "dual-pkg/sub/helper";
// @skjs-expect-error Cannot find module 'dual-pkg/internal' or its corresponding type declarations
import { secret } from "dual-pkg/internal";
// @skjs-expect-error Cannot find module '@acme/exported' or its corresponding type declarations
import { rootTag } from "@acme/exported";
// @skjs-expect-error Cannot find module '@acme/exported/tools/fmt' or its corresponding type declarations
import { format } from "@acme/exported/tools/fmt";

function checkMain(): "from-exports" {
  // @skjs-expect-error Cannot find name
  return mainEntry();
}
