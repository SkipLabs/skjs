// @skjs-expect-error Cannot find module 'untyped' or its corresponding type declarations
import { fromDt } from "untyped";
// @skjs-expect-error Cannot find module '@acme/widgets' or its corresponding type declarations
import { makeWidget } from "@acme/widgets";
import { source } from "own-types";

function checkOwn(): "own" {
  return source;
}
