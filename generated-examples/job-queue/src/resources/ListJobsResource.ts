import { FilterJobsMapper } from "../mappers/FilterJobsMapper.js";
import type {
  Job_skip_id_,
  Job_skip_value_,
  ListJobsParams,
  Job,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListJobsResourceInputs extends SharedCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
}

export class ListJobsResource implements Resource<ListJobsResourceInputs> {
  private readonly ownerId: string | null;
  private readonly queueName: string | null;
  private readonly status: string | null;

  constructor(params: ListJobsParams) {
    this.ownerId = params.ownerId ?? null;
    this.queueName = params.queueName ?? null;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListJobsResourceInputs,
    _context: Context,
  ): EagerCollection<Job_skip_id_, Job_skip_value_> {
    return inputs.jobs.map(
      FilterJobsMapper,
      this.status,
      this.ownerId,
      this.queueName,
    );
  }
}
