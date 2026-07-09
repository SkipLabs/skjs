import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  FeedEventId,
  FeedEvent,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, emit one output pair whose key is the entry's key (the post id), and whose value lists every required field of FeedEvent explicitly: type set to the literal string "POST"; id sourced from the entry's key; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's value's authorId field; postId sourced from the entry's key. The optional commentId field is unconditionally absent from this projection — POST events have no commentId. The optional content field is always present, sourced from the entry's value's content field.
export class PostFeedEventMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  FeedEventId,
  FeedEvent
> {
  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[FeedEventId, FeedEvent]> {
    // > body
    const emits: [FeedEventId, FeedEvent][] = [];
    for (const value of values.toArray()) {
      const event: FeedEvent = {
        type: "POST",
        id: key,
        occurredAt: value.createdAt,
        actorId: value.authorId,
        postId: key,
        content: value.content,
      };
      emits.push([key, event]);
    }
    return emits;
    // < body
  }
}
