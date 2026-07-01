import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { UnreadCountValue, UnreadCountAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumUnreadReducer implements Reducer<
  UnreadCountValue,
  UnreadCountAccum
> {
  initial: UnreadCountAccum = 0;

  add(accum: UnreadCountAccum, value: UnreadCountValue): UnreadCountAccum {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: UnreadCountAccum,
    value: UnreadCountValue,
  ): Nullable<UnreadCountAccum> {
    // > remove
    return accum - value;
    // < remove
  }
}
