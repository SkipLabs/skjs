import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  Room_skip_id_,
  Message,
  Room,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each message entry, emit one output pair whose key is sourced from the entry's value's roomId field (a foreign key to Room, so the new key type is Room_skip_id_), paired with a new value listing every required field of Message explicitly — the id field sourced from the entry's key, the roomId field sourced from the entry's value's roomId field, the authorId field sourced from the entry's value's authorId field, the body field sourced from the entry's value's body field, and the createdAt field sourced from the entry's value's createdAt field. This re-injects the message id on the value side so that downstream consumers consulting by roomId still emit the full Message wire shape.
export class MessageByRoomMapper implements Mapper<
  Message_skip_id_,
  Message_skip_value_,
  Room_skip_id_,
  Message
> {
  mapEntry(
    key: Message_skip_id_,
    values: Values<Message_skip_value_>,
    context: Context,
  ): Iterable<[Room_skip_id_, Message]> {
    // > body
    const emits: [Room_skip_id_, Message][] = [];
    for (const value of values.toArray()) {
      emits.push([
        value.roomId,
        {
          id: key,
          roomId: value.roomId,
          authorId: value.authorId,
          body: value.body,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
