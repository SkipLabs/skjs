import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  MessageOrderKey,
  Message,
  Room_skip_id_,
  Room,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (a message keyed by [createdAt, id]), emit one output pair whose key is sourced from the entry's value roomId field (the Room primary key), paired with the entry's value unchanged. This re-keys messages by their roomId so consumers can look up all messages of a given room by consulting the collection with the roomId. The ascending [createdAt, id] key order is preserved in the entries list because the reactive engine yields per-key values in the order the source entries were keyed. The original composite key components (createdAt, id) are dropped from the new key but are preserved in the value's createdAt and id fields.
export class MessageByRoomMapper implements Mapper<
  MessageOrderKey,
  Message,
  Room_skip_id_,
  Message
> {
  mapEntry(
    key: MessageOrderKey,
    values: Values<Message>,
    context: Context,
  ): Iterable<[Room_skip_id_, Message]> {
    // > body
    const emits: [Room_skip_id_, Message][] = [];
    for (const value of values.toArray()) {
      emits.push([value.roomId, value]);
    }
    return emits;
    // < body
  }
}
