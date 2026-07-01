import { FilterJobByQueueAndStatusMapper } from "../mappers/FilterJobByQueueAndStatusMapper.js";
import type {
  Job_skip_id_,
  Job_skip_value_,
  ListJobsForQueueParams,
  Job,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListJobsForQueueResourceInputs extends SharedCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
}

export class ListJobsForQueueResource implements Resource<ListJobsForQueueResourceInputs> {
  private readonly queueId: string;
  private readonly status: string | null;

  constructor(params: ListJobsForQueueParams) {
    this.queueId = params.queueId;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListJobsForQueueResourceInputs,
    _context: Context,
  ): EagerCollection<Job_skip_id_, Job_skip_value_> {
    return inputs.jobs.map(
      FilterJobByQueueAndStatusMapper,
      this.queueId,
      this.status,
    );
  }
}
