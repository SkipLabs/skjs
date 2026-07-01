import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  Channel_skip_id_,
  Message,
  Channel,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each message entry, emit one output pair whose key is sourced from the entry's value's channelId field (which is the Channel primary key), paired with a new value listing every required field of Message explicitly: id is sourced from the entry's key, channelId is sourced from the entry's value's channelId field, workspaceId is sourced from the entry's value's workspaceId field, authorId is sourced from the entry's value's authorId field, body is sourced from the entry's value's body field, createdAt is sourced from the entry's value's createdAt field, editedAt is sourced from the entry's value's editedAt field.
export class MessagesByChannelMapper implements Mapper<
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
