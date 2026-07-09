import type { Job_skip_id_, Job_skip_value_, Job } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetJobResourceInputs extends SharedCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
}

export class GetJobResource implements Resource<GetJobResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetJobResourceInputs,
    _context: Context,
  ): EagerCollection<Job_skip_id_, Job_skip_value_> {
    return inputs.jobs;
  }
}
