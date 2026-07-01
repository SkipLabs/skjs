import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { MimeCountValue } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<MimeCountValue, MimeCountValue> {
  initial: MimeCountValue = 0;

  add(accum: MimeCountValue, value: MimeCountValue): MimeCountValue {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: MimeCountValue,
    value: MimeCountValue,
  ): Nullable<MimeCountValue> {
    // > remove
    return accum - value;
    // < remove
  }
}
