import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { RedemptionCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumNumberReducer implements Reducer<
  RedemptionCount,
  RedemptionCount
> {
  initial: RedemptionCount = 0;

  add(accum: RedemptionCount, value: RedemptionCount): RedemptionCount {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: RedemptionCount,
    value: RedemptionCount,
  ): Nullable<RedemptionCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
