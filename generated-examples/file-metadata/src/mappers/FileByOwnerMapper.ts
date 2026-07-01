import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerIdKey,
  IndexedFile,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each file entry, emit one output pair whose key is sourced from the entry's value at the ownerId field, paired with a new value that lists every required field of IndexedFile explicitly: id sourced from the entry's input key; ownerId sourced from the entry's value ownerId field; path sourced from the entry's value path field; sizeBytes sourced from the entry's value sizeBytes field; mimeType sourced from the entry's value mimeType field; tags sourced from the entry's value tags field; createdAt sourced from the entry's value createdAt field; updatedAt sourced from the entry's value updatedAt field; the optional hash and description fields are sourced from the entry's value hash and description fields when present.
export class FileByOwnerMapper implements Mapper<
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  OwnerIdKey,
  IndexedFile
> {
  mapEntry(
    key: IndexedFile_skip_id_,
    values: Values<IndexedFile_skip_value_>,
    context: Context,
  ): Iterable<[OwnerIdKey, IndexedFile]> {
    // > body
    const emits: [OwnerIdKey, IndexedFile][] = [];
    for (const value of values.toArray()) {
      const file: IndexedFile = {
        id: key,
        ownerId: value.ownerId,
        path: value.path,
        sizeBytes: value.sizeBytes,
        mimeType: value.mimeType,
        tags: value.tags,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.hash !== undefined && { hash: value.hash }),
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([value.ownerId, file]);
    }
    return emits;
    // < body
  }
}
