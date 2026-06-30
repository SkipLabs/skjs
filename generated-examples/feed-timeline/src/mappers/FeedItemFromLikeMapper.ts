import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { LikeKey, LikeStored, FeedItemKey, FeedItem } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is a FeedItemKey object whose kind is the literal string "like", whose postId is sourced from the entry's key's postId field and whose userId is sourced from the entry's key's userId field (the original Like composite key components are encoded into the new key's postId and userId components). The commentId component of FeedItemKey is absent for this projection. The value enumerates every required field of FeedItem explicitly: kind set to the literal string "like"; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's key's userId field; postId sourced from the entry's key's postId field. The optional commentId field is unconditionally absent from this projection.
export class FeedItemFromLikeMapper implements Mapper<
  LikeKey,
  LikeStored,
  FeedItemKey,
  FeedItem
> {
  mapEntry(
    key: LikeKey,
    values: Values<LikeStored>,
    context: Context,
  ): Iterable<[FeedItemKey, FeedItem]> {
    // > body
    const emits: [FeedItemKey, FeedItem][] = [];
    for (const value of values.toArray()) {
      const outKey: FeedItemKey = {
        kind: "like",
        postId: key.postId,
        userId: key.userId,
      };
      const outValue: FeedItem = {
        kind: "like",
        occurredAt: value.createdAt,
        actorId: key.userId,
        postId: key.postId,
      };
      emits.push([outKey, outValue]);
    }
    return emits;
    // < body
  }
}
