import { fromDt } from "untyped";
import { makeWidget } from "@acme/widgets";
import { source } from "own-types";

function checkAll(): [string, string, "own"] {
  return [fromDt(42), makeWidget("w1").id, source];
}

function badDtCall(): string {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return fromDt("wrong");
}
