import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  StatsSingletonKey,
  IndexStatsAccum,
  FileRecord,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each file entry, emit nothing when the entry's ownerId field does not equal the userId param. Otherwise emit one output pair under the literal-zero key, whose value is a record with fileCount set to one, totalSizeBytes set to the entry's sizeBytes field, mimeTypeCounts set to a record with a single property whose name is the entry's mimeType field and whose value is one, and tagCounts set to a record with one property per element of the entry's tags array (each property name is a tag string, each property value is one — when tags is empty or absent, tagCounts is an empty record). The original file id from the entry's key is dropped because the consumer (stats reducer) aggregates scalars only and does not need the file id.
export class FileStatsContribMapper implements Mapper<
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  StatsSingletonKey,
  IndexStatsAccum
> {
  constructor(private userId: string) {}

  mapEntry(
    key: FileRecord_skip_id_,
    values: Values<FileRecord_skip_value_>,
    context: Context,
  ): Iterable<[StatsSingletonKey, IndexStatsAccum]> {
    // > body
    const arr = values.toArray();
    const emits: [StatsSingletonKey, IndexStatsAccum][] = [];
    for (const value of arr) {
      if (value.ownerId !== this.userId) continue;
      const mimeTypeCounts: Record<string, number> = { [value.mimeType]: 1 };
      const tagCounts: Record<string, number> = {};
      if (value.tags !== undefined) {
        for (const tag of value.tags) {
          tagCounts[tag] = 1;
        }
      }
      const accum: IndexStatsAccum = {
        fileCount: 1,
        totalSizeBytes: value.sizeBytes,
        mimeTypeCounts,
        tagCounts,
      };
      emits.push([0, accum]);
    }
    return emits;
    // < body
  }
}
