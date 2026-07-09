import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { CommentCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<CommentCount, CommentCount> {
  initial: CommentCount = 0;

  add(accum: CommentCount, value: CommentCount): CommentCount {
    // > add
    return accum + value;
    // < add
  }

  remove(accum: CommentCount, value: CommentCount): Nullable<CommentCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
