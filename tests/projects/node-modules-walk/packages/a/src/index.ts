import { tag } from "foo";
import { sharedVal } from "shared";
import { onlyA } from "nested-only";

function useFooFromA(): "nested-a" {
  return tag();
}

function useSharedFromA(): number {
  return sharedVal();
}

function useNestedOnlyFromA(): boolean {
  return onlyA;
}

function badFooFromA(): "root" {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return tag();
}
