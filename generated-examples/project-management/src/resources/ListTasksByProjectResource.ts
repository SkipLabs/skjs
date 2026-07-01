import { TaskByProjectMapper } from "../mappers/TaskByProjectMapper.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  Project_skip_id_,
  Task,
  ListProjectTasksParams,
  Project,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListTasksByProjectResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class ListTasksByProjectResource implements Resource<ListTasksByProjectResourceInputs> {
  private readonly projectId: string;

  constructor(params: ListProjectTasksParams) {
    this.projectId = params.projectId;
  }

  instantiate(
    inputs: ListTasksByProjectResourceInputs,
    _context: Context,
  ): EagerCollection<Project_skip_id_, Task> {
    return inputs.tasks.map(TaskByProjectMapper, this.projectId);
  }
}
