import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  Channel_skip_id_,
  Message,
  Channel,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each message entry, emit a new key sourced from the entry's value's channelId field, paired with a value that carries every required field of Message explicitly — id sourced from the entry's key, channelId sourced from the entry's value's channelId field, workspaceId sourced from the entry's value's workspaceId field, authorId sourced from the entry's value's authorId field, body sourced from the entry's value's body field, createdAt sourced from the entry's value's createdAt field; editedAt is optional, present when the entry's value's editedAt field is present, sourced from the entry's value's editedAt field, absent otherwise.
export class MessageByChannelMapper implements Mapper<
  Message_skip_id_,
  Message_skip_value_,
  Channel_skip_id_,
  Message
> {
  mapEntry(
    key: Message_skip_id_,
    values: Values<Message_skip_value_>,
    context: Context,
  ): Iterable<[Channel_skip_id_, Message]> {
    // > body
    const emits: [Channel_skip_id_, Message][] = [];
    for (const value of values.toArray()) {
      const message: Message = {
        id: key,
        channelId: value.channelId,
        workspaceId: value.workspaceId,
        authorId: value.authorId,
        body: value.body,
        createdAt: value.createdAt,
        ...(value.editedAt !== undefined && { editedAt: value.editedAt }),
      };
      emits.push([value.channelId, message]);
    }
    return emits;
    // < body
  }
}
