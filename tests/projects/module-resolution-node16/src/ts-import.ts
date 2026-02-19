// @skjs-expect-error An import path can only end with a '.ts' extension when 'allowImportingTsExtensions' is enabled.
import { add } from "./utils.ts";

function useTsImport(): number {
  return add(3, 4);
}
