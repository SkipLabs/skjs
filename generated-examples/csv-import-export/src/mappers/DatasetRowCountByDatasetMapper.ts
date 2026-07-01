import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  DatasetRowCountAccum,
  DatasetRow,
  Dataset,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each dataset row entry, emit one output pair whose key is sourced from the entry's key's datasetId field (the Dataset primary key) and whose value is the literal one. The original rowIndex is dropped because the downstream reducer only needs to count occurrences per dataset.
export class DatasetRowCountByDatasetMapper implements Mapper<
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  DatasetRowCountAccum
> {
  mapEntry(
    key: DatasetRow_skip_id_,
    values: Values<DatasetRow_skip_value_>,
    context: Context,
  ): Iterable<[Dataset_skip_id_, DatasetRowCountAccum]> {
    // > body
    const emits: [Dataset_skip_id_, DatasetRowCountAccum][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.datasetId, 1]);
    }
    return emits;
    // < body
  }
}
