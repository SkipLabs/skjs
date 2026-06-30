import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  Post_skip_value_,
  PostLikeCountAccum,
  PostCommentCountAccum,
  Post,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each post entry, consult likeCountByPost for the count values indexed by the entry's key; use the first consulted value when present, otherwise zero — this is the like count. Consult commentCountByPost for the count values indexed by the entry's key; use the first consulted value when present, otherwise zero — this is the comment count. Emit one output pair whose key is the entry's key and whose value enumerates every required field of Post_skip_value_ explicitly: authorId sourced from the entry's value's authorId field; content sourced from the entry's value's content field; createdAt sourced from the entry's value's createdAt field; likeCount set to the resolved like count; commentCount set to the resolved comment count. The optional updatedAt field is present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field; absent otherwise.
export class EnrichPostWithCountsMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(
    private likeCountByPost: EagerCollection<Post_skip_id_, PostLikeCountAccum>,
    private commentCountByPost: EagerCollection<
      Post_skip_id_,
      PostCommentCountAccum
    >,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    const entries = values.toArray();
    const stored = entries[0];
    if (stored === undefined) return [];

    const likeCounts = this.likeCountByPost.getArray(key);
    const likeCount = likeCounts[0] ?? 0;

    const commentCounts = this.commentCountByPost.getArray(key);
    const commentCount = commentCounts[0] ?? 0;

    const out: Post_skip_value_ = {
      authorId: stored.authorId,
      content: stored.content,
      createdAt: stored.createdAt,
      likeCount,
      commentCount,
      ...(stored.updatedAt !== undefined && { updatedAt: stored.updatedAt }),
    };

    return [[key, out]];
    // < body
  }
}
