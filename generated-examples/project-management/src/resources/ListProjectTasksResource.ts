import { FilterTaskByProjectStatusAssigneeMapper } from "../mappers/FilterTaskByProjectStatusAssigneeMapper.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  ListTasksParams,
  Task,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListProjectTasksResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class ListProjectTasksResource implements Resource<ListProjectTasksResourceInputs> {
  private readonly assigneeId: string | null;
  private readonly projectId: string;
  private readonly status: string | null;

  constructor(params: ListTasksParams) {
    this.assigneeId = params.assigneeId ?? null;
    this.projectId = params.projectId;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListProjectTasksResourceInputs,
    _context: Context,
  ): EagerCollection<Task_skip_id_, Task_skip_value_> {
    return inputs.tasks.map(
      FilterTaskByProjectStatusAssigneeMapper,
      this.projectId,
      this.status,
      this.assigneeId,
    );
  }
}
