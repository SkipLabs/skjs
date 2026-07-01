import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  FeedItemKey,
  FeedItem,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, emit one output pair whose key is a FeedItemKey object whose kind is the literal string "post" and whose postId is sourced from the entry's key (the post id). The userId and commentId components of FeedItemKey are absent for this projection. The value enumerates every required field of FeedItem explicitly: kind set to the literal string "post"; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's value's authorId field; postId sourced from the entry's key. The optional commentId field is unconditionally absent from this projection.
export class FeedItemFromPostMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  FeedItemKey,
  FeedItem
> {
  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[FeedItemKey, FeedItem]> {
    // > body
    const emits: [FeedItemKey, FeedItem][] = [];
    for (const value of values.toArray()) {
      const feedKey: FeedItemKey = { kind: "post", postId: key };
      const feedItem: FeedItem = {
        kind: "post",
        occurredAt: value.createdAt,
        actorId: value.authorId,
        postId: key,
      };
      emits.push([feedKey, feedItem]);
    }
    return emits;
    // < body
  }
}
