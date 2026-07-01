import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  FileRecord,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each file entry, emit the entry unchanged when the entry's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterFilesByOwnerMapper implements Mapper<
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  FileRecord_skip_id_,
  FileRecord_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: FileRecord_skip_id_,
    values: Values<FileRecord_skip_value_>,
    context: Context,
  ): Iterable<[FileRecord_skip_id_, FileRecord_skip_value_]> {
    // > body
    const emits: [FileRecord_skip_id_, FileRecord_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
