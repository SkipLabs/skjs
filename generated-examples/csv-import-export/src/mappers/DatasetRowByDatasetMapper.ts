import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  DatasetRowByDatasetValue,
  DatasetRow,
  Dataset,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each dataset row entry, emit one output pair whose key is sourced from the entry's key's datasetId field (the Dataset primary key), paired with a new value whose rowIndex is sourced from the entry's key's rowIndex field (re-injected from the composite PK, which _skip_value_ excludes) and whose values and createdAt are sourced from the entry's value. This preserves rowIndex so listDatasetRows can sort/paginate.
export class DatasetRowByDatasetMapper implements Mapper<
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  DatasetRowByDatasetValue
> {
  mapEntry(
    key: DatasetRow_skip_id_,
    values: Values<DatasetRow_skip_value_>,
    context: Context,
  ): Iterable<[Dataset_skip_id_, DatasetRowByDatasetValue]> {
    // > body
    const emits: [Dataset_skip_id_, DatasetRowByDatasetValue][] = [];
    for (const value of values) {
      emits.push([
        key.datasetId,
        {
          rowIndex: key.rowIndex,
          values: value.values,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
