import { greet } from "foo";
import { answer } from "bar";
import { legacy } from "legacy-index";
import { add } from "ts-fallback";
import { tag } from "@acme/pkg";

function useAll(): [string, number, boolean, number, "acme"] {
  return [greet("world"), answer, legacy(1), add(2, 3), tag()];
}

function badAnswer(): string {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return answer;
}

function badGreet(): string {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return greet(123);
}
