import { mainEntry } from "dual-pkg";
import { utilFn } from "dual-pkg/utils";
import { helper } from "dual-pkg/sub/helper";
// @skjs-expect-error Package subpath './internal' is not defined by 'exports' in 'dual-pkg/package.json'
import { secret } from "dual-pkg/internal";
import { rootTag } from "@acme/exported";
import { format } from "@acme/exported/tools/fmt";

function checkAll(): ["from-exports", number, number, "acme-root", string] {
  return [mainEntry(), utilFn(1), helper("abc"), rootTag, format(42)];
}

function badUtil(): number {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return utilFn("nope");
}
