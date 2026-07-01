import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Note_skip_id_, Note_skip_value_, Note } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each note entry, emit the entry unchanged when the entry's value's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterNoteByOwnerMapper implements Mapper<
  Note_skip_id_,
  Note_skip_value_,
  Note_skip_id_,
  Note_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Note_skip_id_,
    values: Values<Note_skip_value_>,
    context: Context,
  ): Iterable<[Note_skip_id_, Note_skip_value_]> {
    // > body
    const emits: [Note_skip_id_, Note_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
