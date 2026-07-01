import { FilterTodosByOwnerMapper } from "../mappers/FilterTodosByOwnerMapper.js";
import type {
  Todo_skip_id_,
  Todo_skip_value_,
  ListTodosParams,
  Todo,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListTodosResourceInputs extends SharedCollections {
  readonly todos: EagerCollection<Todo_skip_id_, Todo_skip_value_>;
}

export class ListTodosResource implements Resource<ListTodosResourceInputs> {
  private readonly userId: string;

  constructor(params: ListTodosParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListTodosResourceInputs,
    _context: Context,
  ): EagerCollection<Todo_skip_id_, Todo_skip_value_> {
    return inputs.todos.map(FilterTodosByOwnerMapper, this.userId);
  }
}
