import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { PostCommentCount, PostCommentCountAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumCommentReducer implements Reducer<
  PostCommentCount,
  PostCommentCountAccum
> {
  initial: PostCommentCountAccum = 0;

  add(
    accum: PostCommentCountAccum,
    value: PostCommentCount,
  ): PostCommentCountAccum {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: PostCommentCountAccum,
    value: PostCommentCount,
  ): Nullable<PostCommentCountAccum> {
    // > remove
    return accum - value;
    // < remove
  }
}
