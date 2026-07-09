import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { RunningJobCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<RunningJobCount, RunningJobCount> {
  initial: RunningJobCount = 0;

  add(accum: RunningJobCount, value: RunningJobCount): RunningJobCount {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: RunningJobCount,
    value: RunningJobCount,
  ): Nullable<RunningJobCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
