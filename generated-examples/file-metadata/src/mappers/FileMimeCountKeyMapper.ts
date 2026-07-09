import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerMimeKey,
  MimeCountValue,
  IndexedFile,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each file entry, emit one output pair whose key is a composite object built from the entry's value's ownerId field and the entry's value's mimeType field, and whose value is the literal one. The original file id from the input key is dropped because the consumer aggregates counts by (ownerId, mimeType) and does not need the individual file id.
export class FileMimeCountKeyMapper implements Mapper<
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerMimeKey,
  MimeCountValue
> {
  mapEntry(
    key: IndexedFile_skip_id_,
    values: Values<IndexedFile_skip_value_>,
    context: Context,
  ): Iterable<[OwnerMimeKey, MimeCountValue]> {
    // > body
    const emits: [OwnerMimeKey, MimeCountValue][] = [];
    for (const value of values.toArray()) {
      const compositeKey: OwnerMimeKey = {
        mimeType: value.mimeType,
        ownerId: value.ownerId,
      };
      emits.push([compositeKey, 1]);
    }
    return emits;
    // < body
  }
}
