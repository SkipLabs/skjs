import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { UnreadMarker } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<UnreadMarker, UnreadMarker> {
  initial: UnreadMarker = 0;

  add(accum: UnreadMarker, value: UnreadMarker): UnreadMarker {
    // > add
    return accum + value;
    // < add
  }

  remove(accum: UnreadMarker, value: UnreadMarker): Nullable<UnreadMarker> {
    // > remove
    return accum - value;
    // < remove
  }
}
