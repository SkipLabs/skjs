import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  LikeIncrement,
  CommentLike,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment-like entry, emit one output pair whose key is sourced from the entry's key's commentId field and whose value is the literal number one. The original userId from from[0] is dropped because the consumer (a sum-reducer counting likes per comment) does not need it.
export class CommentLikeCountMapper implements Mapper<
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  LikeIncrement
> {
  mapEntry(
    key: CommentLike_skip_id_,
    values: Values<CommentLike_skip_value_>,
    context: Context,
  ): Iterable<[Comment_skip_id_, LikeIncrement]> {
    // > body
    const emits: [Comment_skip_id_, LikeIncrement][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.commentId, 1]);
    }
    return emits;
    // < body
  }
}
