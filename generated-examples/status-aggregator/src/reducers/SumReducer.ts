import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ComponentStatusCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<
  ComponentStatusCount,
  ComponentStatusCount
> {
  initial: ComponentStatusCount = 0;

  add(
    accum: ComponentStatusCount,
    value: ComponentStatusCount,
  ): ComponentStatusCount {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: ComponentStatusCount,
    value: ComponentStatusCount,
  ): Nullable<ComponentStatusCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
