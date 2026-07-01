import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  CommentStored,
  CommentWithLikeCount,
  LikeIncrement,
  Comment,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each comment entry, look up the per-comment like count in params.likeCountByComment by the entry's key (the comment id), defaulting to 0 when absent. Emit one output pair whose key is the entry's key unchanged and whose value is a CommentWithLikeCount record assembled by setting id to the entry's key (the commentId), copying every field of the CommentStored value (threadKey, parentCommentId, authorId, body, createdAt, updatedAt), and setting likeCount to the looked-up count. The mapper does the full assembly in its body.
export class CommentWithLikeCountByIdMapper implements Mapper<
  Comment_skip_id_,
  CommentStored,
  Comment_skip_id_,
  CommentWithLikeCount
> {
  constructor(
    private likeCountByComment: EagerCollection<
      Comment_skip_id_,
      LikeIncrement
    >,
  ) {}

  mapEntry(
    key: Comment_skip_id_,
    values: Values<CommentStored>,
    context: Context,
  ): Iterable<[Comment_skip_id_, CommentWithLikeCount]> {
    // > body
    const likeCountByComment = this.likeCountByComment;
    const emits: [Comment_skip_id_, CommentWithLikeCount][] = [];
    for (const value of values.toArray()) {
      const likeCounts = likeCountByComment.getArray(key);
      let likeCount = 0;
      if (likeCounts.length > 0) {
        const first = likeCounts[0];
        if (first !== undefined) likeCount = first;
      }
      const out: CommentWithLikeCount = {
        id: key,
        threadKey: value.threadKey,
        ...(value.parentCommentId !== undefined && {
          parentCommentId: value.parentCommentId,
        }),
        authorId: value.authorId,
        body: value.body,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        likeCount,
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
