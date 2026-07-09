import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  CommentStored,
  Comment_skip_value_,
  LikeCount,
  Comment,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each comment entry, consult likeCountByComment for the counts indexed by the entry's key; sum the consulted values to obtain the total like count (zero when no values are consulted). Emit one output pair whose key is the entry's key and whose value lists every field of Comment explicitly: authorId sourced from the entry's value's authorId field; body sourced from the entry's value's body field; createdAt sourced from the entry's value's createdAt field; parentCommentId is optional — present when the entry's value carries a parentCommentId field, sourced from the entry's value's parentCommentId field; absent otherwise; updatedAt is optional — present when the entry's value carries an updatedAt field, sourced from the entry's value's updatedAt field; absent otherwise; likeCount sourced from the summed count.
export class AssembleCommentMapper implements Mapper<
  Comment_skip_id_,
  CommentStored,
  Comment_skip_id_,
  Comment_skip_value_
> {
  constructor(
    private likeCountByComment: EagerCollection<Comment_skip_id_, LikeCount>,
  ) {}

  mapEntry(
    key: Comment_skip_id_,
    values: Values<CommentStored>,
    context: Context,
  ): Iterable<[Comment_skip_id_, Comment_skip_value_]> {
    // > body
    const stored = values.toArray()[0];
    if (stored === undefined) return [];
    const counts = this.likeCountByComment.getArray(key);
    let total = 0;
    for (const c of counts) total += c;
    const out: Comment_skip_value_ = {
      authorId: stored.authorId,
      body: stored.body,
      createdAt: stored.createdAt,
      ...(stored.parentCommentId !== undefined && {
        parentCommentId: stored.parentCommentId,
      }),
      ...(stored.updatedAt !== undefined && { updatedAt: stored.updatedAt }),
      likeCount: total,
    };
    return [[key, out]];
    // < body
  }
}
