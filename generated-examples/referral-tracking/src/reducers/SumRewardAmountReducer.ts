import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { RewardAmountMinorUnits } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumRewardAmountReducer implements Reducer<
  RewardAmountMinorUnits,
  RewardAmountMinorUnits
> {
  initial: RewardAmountMinorUnits = 0;

  add(
    accum: RewardAmountMinorUnits,
    value: RewardAmountMinorUnits,
  ): RewardAmountMinorUnits {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: RewardAmountMinorUnits,
    value: RewardAmountMinorUnits,
  ): Nullable<RewardAmountMinorUnits> {
    // > remove
    return accum - value;
    // < remove
  }
}
