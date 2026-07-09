import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerHashKey,
  IndexedFile,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each file entry, when the entry's value carries a hash field (present), emit one output pair whose key is a composite object built from the entry's value's ownerId field and the entry's value's hash field, paired with a new value that lists every required field of IndexedFile explicitly: id sourced from the entry's input key; ownerId sourced from the entry's value ownerId field; path sourced from the entry's value path field; sizeBytes sourced from the entry's value sizeBytes field; mimeType sourced from the entry's value mimeType field; tags sourced from the entry's value tags field; createdAt sourced from the entry's value createdAt field; updatedAt sourced from the entry's value updatedAt field; hash sourced from the entry's value hash field; description sourced from the entry's value description field when present. Otherwise emit nothing.
export class FileByOwnerHashMapper implements Mapper<
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerHashKey,
  IndexedFile
> {
  mapEntry(
    key: IndexedFile_skip_id_,
    values: Values<IndexedFile_skip_value_>,
    context: Context,
  ): Iterable<[OwnerHashKey, IndexedFile]> {
    // > body
    const emits: [OwnerHashKey, IndexedFile][] = [];
    for (const value of values.toArray()) {
      if (value.hash === undefined) continue;
      const compositeKey: OwnerHashKey = {
        hash: value.hash,
        ownerId: value.ownerId,
      };
      const file: IndexedFile = {
        id: key,
        ownerId: value.ownerId,
        path: value.path,
        sizeBytes: value.sizeBytes,
        mimeType: value.mimeType,
        tags: value.tags,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        hash: value.hash,
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([compositeKey, file]);
    }
    return emits;
    // < body
  }
}
