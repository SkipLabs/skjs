import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { CountValue, CountAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<CountValue, CountAccum> {
  initial: CountAccum = 0;

  add(accum: CountAccum, value: CountValue): CountAccum {
    // > add
    return accum + value;
    // < add
  }

  remove(accum: CountAccum, value: CountValue): Nullable<CountAccum> {
    // > remove
    return accum - value;
    // < remove
  }
}
