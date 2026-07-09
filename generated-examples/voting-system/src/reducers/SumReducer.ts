import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { VoteCountValue } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<VoteCountValue, VoteCountValue> {
  initial: VoteCountValue = 0;

  add(accum: VoteCountValue, value: VoteCountValue): VoteCountValue {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: VoteCountValue,
    value: VoteCountValue,
  ): Nullable<VoteCountValue> {
    // > remove
    return accum - value;
    // < remove
  }
}
