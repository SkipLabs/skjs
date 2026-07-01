import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  FeedItemKey,
  FeedItem,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is a FeedItemKey object whose kind is the literal string "comment", whose postId is sourced from the entry's value's postId field and whose commentId is sourced from the entry's key (the original Comment.id is encoded into the new key's commentId component). The userId component of FeedItemKey is absent for this projection. The value enumerates every required field of FeedItem explicitly: kind set to the literal string "comment"; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's value's authorId field; postId sourced from the entry's value's postId field. The optional commentId field is always present, sourced from the entry's key (the comment id).
export class FeedItemFromCommentMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  FeedItemKey,
  FeedItem
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[FeedItemKey, FeedItem]> {
    // > body
    const emits: [FeedItemKey, FeedItem][] = [];
    for (const value of values.toArray()) {
      const feedKey: FeedItemKey = {
        kind: "comment",
        postId: value.postId,
        commentId: key,
      };
      const feedItem: FeedItem = {
        kind: "comment",
        occurredAt: value.createdAt,
        actorId: value.authorId,
        postId: value.postId,
        commentId: key,
      };
      emits.push([feedKey, feedItem]);
    }
    return emits;
    // < body
  }
}
