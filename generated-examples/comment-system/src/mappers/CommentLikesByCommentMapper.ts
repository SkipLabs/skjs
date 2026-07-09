import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  CommentLike,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment like entry, emit one output pair whose key is sourced from the entry's key's commentId field (the original CommentLike.commentId is encoded into the new key) and whose value lists every required field of CommentLike explicitly: commentId sourced from the entry's key's commentId field; userId sourced from the entry's key's userId field (the original CommentLike.userId is preserved in the value as userId); createdAt sourced from the entry's value's createdAt field.
export class CommentLikesByCommentMapper implements Mapper<
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
