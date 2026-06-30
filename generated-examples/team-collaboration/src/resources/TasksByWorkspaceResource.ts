import { TasksByWorkspaceMapper } from "../mappers/TasksByWorkspaceMapper.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  Workspace_skip_id_,
  Task,
  Workspace,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface TasksByWorkspaceResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class TasksByWorkspaceResource implements Resource<TasksByWorkspaceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: TasksByWorkspaceResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Task> {
    const tasksByWorkspace = inputs.tasks.map(TasksByWorkspaceMapper);
    return tasksByWorkspace;
  }
}
