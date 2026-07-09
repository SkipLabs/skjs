import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ActiveLoanCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<ActiveLoanCount, ActiveLoanCount> {
  initial: ActiveLoanCount = 0;

  add(accum: ActiveLoanCount, value: ActiveLoanCount): ActiveLoanCount {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: ActiveLoanCount,
    value: ActiveLoanCount,
  ): Nullable<ActiveLoanCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
