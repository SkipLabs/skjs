import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  CommentLike,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment-like entry, emit one output pair whose key is sourced from the entry's key's commentId field and whose value is a record listing every required field of CommentLike explicitly — commentId sourced from the entry's key's commentId field; userId sourced from the entry's key's userId field; createdAt sourced from the entry's value's createdAt field. The original userId from from[0] is preserved in the output value as the userId field so downstream consumers can identify who liked. The original commentId from from[0] is encoded into the new key AND preserved in the output value as the commentId field.
export class CommentLikeByCommentIdMapper implements Mapper<
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  CommentLike
> {
  mapEntry(
    key: CommentLike_skip_id_,
    values: Values<CommentLike_skip_value_>,
    context: Context,
  ): Iterable<[Comment_skip_id_, CommentLike]> {
    // > body
    const emits: [Comment_skip_id_, CommentLike][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.commentId,
        {
          commentId: key.commentId,
          userId: key.userId,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
