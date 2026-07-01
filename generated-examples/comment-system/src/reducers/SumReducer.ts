import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { LikeIncrement } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<LikeIncrement, LikeIncrement> {
  initial: LikeIncrement = 0;

  add(accum: LikeIncrement, value: LikeIncrement): LikeIncrement {
    // > add
    return accum + value;
    // < add
  }

  remove(accum: LikeIncrement, value: LikeIncrement): Nullable<LikeIncrement> {
    // > remove
    return accum - value;
    // < remove
  }
}
