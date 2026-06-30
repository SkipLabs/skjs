import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  User_skip_id_,
  Note,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each note entry, emit one output pair whose key is sourced from the entry's value's ownerId field, and whose value lists every required field of Note explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; title sourced from the entry's value's title field; content sourced from the entry's value's content field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field. The original key component id is preserved in the value as the id field, so the consumer can reconstruct the full Note entity.
export class NotesByOwnerMapper implements Mapper<
  Note_skip_id_,
  Note_skip_value_,
  User_skip_id_,
  Note
> {
  mapEntry(
    key: Note_skip_id_,
    values: Values<Note_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Note]> {
    // > body
    const emits: [User_skip_id_, Note][] = [];
    for (const value of values.toArray()) {
      const note: Note = {
        id: key,
        ownerId: value.ownerId,
        title: value.title,
        content: value.content,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
      };
      emits.push([value.ownerId, note]);
    }
    return emits;
    // < body
  }
}
