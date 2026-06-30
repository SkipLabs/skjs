import type {
  Project_skip_id_,
  Project,
  Project_skip_value_,
  Task_skip_id_,
  Task,
  Task_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_projects = inputs.projects;
  const output_tasks = inputs.tasks;
  const output_users = inputs.users;
  return {
    projects: output_projects,
    tasks: output_tasks,
    users: output_users,
  };
}
