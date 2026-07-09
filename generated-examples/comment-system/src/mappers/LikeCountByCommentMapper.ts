import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  LikeCount,
  CommentLike,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment like entry, emit one output pair whose key is sourced from the entry's key's commentId field (the original CommentLike.commentId is encoded into the new key) and whose value is the literal one. The userId is dropped: this collection feeds AssembleCommentMapper which aggregates like counts per comment and never needs to identify the individual liking user.
export class LikeCountByCommentMapper implements Mapper<
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  LikeCount
> {
  mapEntry(
    key: CommentLike_skip_id_,
    values: Values<CommentLike_skip_value_>,
    context: Context,
  ): Iterable<[Comment_skip_id_, LikeCount]> {
    // > body
    const emits: [Comment_skip_id_, LikeCount][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.commentId, 1]);
    }
    return emits;
    // < body
  }
}
