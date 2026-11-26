import { tag } from "foo";
import { sharedVal } from "shared";
// @skjs-expect-error Cannot find module 'nested-only' or its corresponding type declarations
import { onlyA } from "nested-only";

// Pre-#612: flat lookup hits root node_modules/foo ("root"), not
// packages/a/node_modules/foo ("nested-a").
function useFooFromA(): "nested-a" {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return tag();
}

function useSharedFromA(): number {
  return sharedVal();
}

function useNestedOnlyFromA(): boolean {
  // @skjs-expect-error Cannot find name
  return onlyA;
}
