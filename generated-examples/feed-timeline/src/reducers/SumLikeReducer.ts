import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { PostLikeCount, PostLikeCountAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumLikeReducer implements Reducer<
  PostLikeCount,
  PostLikeCountAccum
> {
  initial: PostLikeCountAccum = 0;

  add(accum: PostLikeCountAccum, value: PostLikeCount): PostLikeCountAccum {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: PostLikeCountAccum,
    value: PostLikeCount,
  ): Nullable<PostLikeCountAccum> {
    // > remove
    return accum - value;
    // < remove
  }
}
