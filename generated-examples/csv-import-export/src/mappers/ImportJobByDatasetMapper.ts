import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ImportJob_skip_id_,
  ImportJob_skip_value_,
  Dataset_skip_id_,
  ImportJobByDatasetValue,
  ImportJob,
  Dataset,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each import job entry, emit one output pair whose key is sourced from the entry's datasetId field (the Dataset primary key), paired with a new value whose id is sourced from the entry's key (the original ImportJob primary key, which _skip_value_ excludes) and whose ownerId, status, totalRows, processedRows, failedRows, errorMessage, createdAt, startedAt, finishedAt are sourced from the entry's value. This re-injects the job id on the value side so listImportJobs can return full ImportJob responses.
export class ImportJobByDatasetMapper implements Mapper<
  ImportJob_skip_id_,
  ImportJob_skip_value_,
  Dataset_skip_id_,
  ImportJobByDatasetValue
> {
  mapEntry(
    key: ImportJob_skip_id_,
    values: Values<ImportJob_skip_value_>,
    context: Context,
  ): Iterable<[Dataset_skip_id_, ImportJobByDatasetValue]> {
    // > body
    const emits: [Dataset_skip_id_, ImportJobByDatasetValue][] = [];
    for (const value of values.toArray()) {
      const out: ImportJobByDatasetValue = {
        id: key,
        ownerId: value.ownerId,
        status: value.status,
        totalRows: value.totalRows,
        processedRows: value.processedRows,
        failedRows: value.failedRows,
        createdAt: value.createdAt,
        ...(value.errorMessage !== undefined && {
          errorMessage: value.errorMessage,
        }),
        ...(value.startedAt !== undefined && { startedAt: value.startedAt }),
        ...(value.finishedAt !== undefined && { finishedAt: value.finishedAt }),
      };
      emits.push([value.datasetId, out]);
    }
    return emits;
    // < body
  }
}
