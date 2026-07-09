import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Like_skip_id_,
  Like_skip_value_,
  FeedEventId,
  FeedEvent,
  Like,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is a string formed by concatenating the entry's key's postId field, the literal pipe character, and the entry's key's userId field, and whose value lists every required field of FeedEvent explicitly: type set to the literal string "LIKE"; id set to the same concatenated string used as key; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's key's userId field; postId sourced from the entry's key's postId field. The original Like.postId is encoded into the new key (as the leading component of the concatenated string) and preserved on the value side as postId. The original Like.userId is encoded into the new key (as the trailing component of the concatenated string) and preserved on the value side as actorId. The optional commentId field is unconditionally absent from this projection — LIKE events have no commentId. The optional content field is unconditionally absent from this projection — LIKE events have no content.
export class LikeFeedEventMapper implements Mapper<
  Like_skip_id_,
  Like_skip_value_,
  FeedEventId,
  FeedEvent
> {
  mapEntry(
    key: Like_skip_id_,
    values: Values<Like_skip_value_>,
    context: Context,
  ): Iterable<[FeedEventId, FeedEvent]> {
    // > body
    const emits: [FeedEventId, FeedEvent][] = [];
    const id = `${key.postId}|${key.userId}`;
    for (const value of values.toArray()) {
      const feedEvent: FeedEvent = {
        type: "LIKE",
        id,
        occurredAt: value.createdAt,
        actorId: key.userId,
        postId: key.postId,
      };
      emits.push([id, feedEvent]);
    }
    return emits;
    // < body
  }
}
