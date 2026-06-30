import type { Todo_skip_id_, Todo_skip_value_, Todo } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTodoResourceInputs extends SharedCollections {
  readonly todos: EagerCollection<Todo_skip_id_, Todo_skip_value_>;
}

export class GetTodoResource implements Resource<GetTodoResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetTodoResourceInputs,
    _context: Context,
  ): EagerCollection<Todo_skip_id_, Todo_skip_value_> {
    return inputs.todos;
  }
}
