import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { DatasetRowCountAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<
  DatasetRowCountAccum,
  DatasetRowCountAccum
> {
  initial: DatasetRowCountAccum = 0;

  add(
    accum: DatasetRowCountAccum,
    value: DatasetRowCountAccum,
  ): DatasetRowCountAccum {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: DatasetRowCountAccum,
    value: DatasetRowCountAccum,
  ): Nullable<DatasetRowCountAccum> {
    // > remove
    return accum - value;
    // < remove
  }
}
