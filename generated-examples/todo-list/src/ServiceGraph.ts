import type {
  Todo_skip_id_,
  Todo,
  Todo_skip_value_,
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
  readonly todos: EagerCollection<Todo_skip_id_, Todo_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly todos: EagerCollection<Todo_skip_id_, Todo_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_todos = inputs.todos;
  const output_users = inputs.users;
  return { todos: output_todos, users: output_users };
}
