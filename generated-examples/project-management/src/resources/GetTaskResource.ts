import { FilterTaskByIdAndProjectMapper } from "../mappers/FilterTaskByIdAndProjectMapper.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  GetTaskParams,
  Task,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTaskResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class GetTaskResource implements Resource<GetTaskResourceInputs> {
  private readonly projectId: string;
  private readonly taskId: string;

  constructor(params: GetTaskParams) {
    this.projectId = params.projectId;
    this.taskId = params.taskId;
  }

  instantiate(
    inputs: GetTaskResourceInputs,
    _context: Context,
  ): EagerCollection<Task_skip_id_, Task_skip_value_> {
    return inputs.tasks.map(
      FilterTaskByIdAndProjectMapper,
      this.projectId,
      this.taskId,
    );
  }
}
