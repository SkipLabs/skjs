import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  MessageOrderKey,
  Message,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each message entry, emit one output pair whose key is a MessageOrderKey composite of the entry's value createdAt field (as the primary sort component, ascending) and the entry's key id field (as tiebreaker), paired with a full Message record. The output value lists every required field of Message explicitly: id sourced from the entry's key; roomId sourced from the entry's value roomId field; authorId sourced from the entry's value authorId field; content sourced from the entry's value content field; createdAt sourced from the entry's value createdAt field. The original id component of the input key is encoded into the new key as the tiebreaker component AND re-injected into the value. Downstream consumers filter by roomId (carried in the value) and by since (compared against createdAt in the value or key).
export class MessageByRoomOrderedMapper implements Mapper<
  Message_skip_id_,
  Message_skip_value_,
  MessageOrderKey,
  Message
> {
  mapEntry(
    key: Message_skip_id_,
    values: Values<Message_skip_value_>,
    context: Context,
  ): Iterable<[MessageOrderKey, Message]> {
    // > body
    const emits: [MessageOrderKey, Message][] = [];
    for (const value of values.toArray()) {
      const orderKey: MessageOrderKey = {
        createdAt: value.createdAt,
        id: key,
      };
      const message: Message = {
        id: key,
        roomId: value.roomId,
        authorId: value.authorId,
        content: value.content,
        createdAt: value.createdAt,
      };
      emits.push([orderKey, message]);
    }
    return emits;
    // < body
  }
}
