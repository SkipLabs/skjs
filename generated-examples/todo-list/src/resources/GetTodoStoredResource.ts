import type { Todo_skip_id_, Todo_skip_value_, Todo } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetTodoStoredResourceInputs extends SharedCollections {
  readonly todos: EagerCollection<Todo_skip_id_, Todo_skip_value_>;
}

export class GetTodoStoredResource implements Resource<GetTodoStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetTodoStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Todo_skip_id_, Todo_skip_value_> {
    return inputs.todos;
  }
}
