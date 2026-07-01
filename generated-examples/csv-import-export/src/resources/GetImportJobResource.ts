import type {
  ImportJob_skip_id_,
  ImportJob_skip_value_,
  ImportJob,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetImportJobResourceInputs extends SharedCollections {
  readonly importJobs: EagerCollection<
    ImportJob_skip_id_,
    ImportJob_skip_value_
  >;
}

export class GetImportJobResource implements Resource<GetImportJobResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetImportJobResourceInputs,
    _context: Context,
  ): EagerCollection<ImportJob_skip_id_, ImportJob_skip_value_> {
    return inputs.importJobs;
  }
}
