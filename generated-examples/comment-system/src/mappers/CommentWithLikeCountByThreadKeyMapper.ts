import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ThreadKey,
  Comment_skip_id_,
  CommentWithLikeCount,
  CommentStored,
  LikeIncrement,
  Comment,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each threadKey key, iterate the values associated with the key — each value is a commentId — and for each commentId, look up the CommentStored row in params.comments by the commentId and the like count in params.likeCountByComment by the commentId (defaulting to 0), emit one output pair whose key is the threadKey and whose value is the assembled CommentWithLikeCount record. The CommentWithLikeCount is built by setting id to the iterated commentId (sourced from the from[1] value), copying every field of the CommentStored row (threadKey, parentCommentId, authorId, body, createdAt, updatedAt), and setting likeCount to the looked-up count. The upstream CommentByThreadKeyMapper re-keys comments from commentId to threadKey, so multiple commentIds may accumulate under one threadKey — singleton-only access would raise on any thread with two or more comments. The mapper does the full join in its body — no aggregation is deferred to the api handler.
export class CommentWithLikeCountByThreadKeyMapper implements Mapper<
  ThreadKey,
  Comment_skip_id_,
  ThreadKey,
  CommentWithLikeCount
> {
  constructor(
    private comments: EagerCollection<Comment_skip_id_, CommentStored>,
    private likeCountByComment: EagerCollection<
      Comment_skip_id_,
      LikeIncrement
    >,
  ) {}

  mapEntry(
    key: ThreadKey,
    values: Values<Comment_skip_id_>,
    context: Context,
  ): Iterable<[ThreadKey, CommentWithLikeCount]> {
    // > body
    const emits: [ThreadKey, CommentWithLikeCount][] = [];
    for (const commentId of values.toArray()) {
      const stored = this.comments.getArray(commentId)[0];
      if (stored === undefined) continue;
      const likeCount = this.likeCountByComment.getArray(commentId)[0] ?? 0;
      const out: CommentWithLikeCount = {
        id: commentId,
        threadKey: stored.threadKey,
        authorId: stored.authorId,
        body: stored.body,
        createdAt: stored.createdAt,
        updatedAt: stored.updatedAt,
        likeCount,
        ...(stored.parentCommentId !== undefined && {
          parentCommentId: stored.parentCommentId,
        }),
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
