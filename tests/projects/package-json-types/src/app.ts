// @skjs-expect-error Cannot find module 'foo' or its corresponding type declarations
import { greet } from "foo";
// @skjs-expect-error Cannot find module 'bar' or its corresponding type declarations
import { answer } from "bar";
import { legacy } from "legacy-index";
// @skjs-expect-error Cannot find module 'ts-fallback' or its corresponding type declarations
import { add } from "ts-fallback";
// @skjs-expect-error Cannot find module '@acme/pkg' or its corresponding type declarations
import { tag } from "@acme/pkg";

function useLegacy(): boolean {
  return legacy(1);
}
