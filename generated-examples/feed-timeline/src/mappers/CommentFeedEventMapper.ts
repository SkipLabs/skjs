import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  FeedEventId,
  FeedEvent,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is the entry's key (the comment id), and whose value lists every required field of FeedEvent explicitly: type set to the literal string "COMMENT"; id sourced from the entry's key; occurredAt sourced from the entry's value's createdAt field; actorId sourced from the entry's value's authorId field; postId sourced from the entry's value's postId field. The optional commentId field is always present, sourced from the entry's key. The optional content field is always present, sourced from the entry's value's content field. The original Comment.id is preserved in the value as commentId (and as id).
export class CommentFeedEventMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  FeedEventId,
  FeedEvent
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[FeedEventId, FeedEvent]> {
    // > body
    const emits: [FeedEventId, FeedEvent][] = [];
    for (const value of values.toArray()) {
      const event: FeedEvent = {
        type: "COMMENT",
        id: key,
        occurredAt: value.createdAt,
        actorId: value.authorId,
        postId: value.postId,
        commentId: key,
        content: value.content,
      };
      emits.push([key, event]);
    }
    return emits;
    // < body
  }
}
