import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Note_skip_id_, Note_skip_value_, Note } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each note entry, when the entry's key does not equal the noteId param, emit nothing. Otherwise emit one output pair whose key is the literal zero and whose value lists every required field of Note explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; title sourced from the entry's value's title field; content sourced from the entry's value's content field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field.
export class GetNoteMapper implements Mapper<
  Note_skip_id_,
  Note_skip_value_,
  0,
  Note
> {
  constructor(private noteId: string) {}

  mapEntry(
    key: Note_skip_id_,
    values: Values<Note_skip_value_>,
    context: Context,
  ): Iterable<[0, Note]> {
    // > body
    if (key !== this.noteId) return [];
    const emits: [0, Note][] = [];
    for (const value of values.toArray()) {
      emits.push([
        0,
        {
          id: key,
          ownerId: value.ownerId,
          title: value.title,
          content: value.content,
          createdAt: value.createdAt,
          updatedAt: value.updatedAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
