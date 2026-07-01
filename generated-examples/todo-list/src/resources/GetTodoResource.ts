import { FilterTodoByIdAndOwnerMapper } from "../mappers/FilterTodoByIdAndOwnerMapper.js";
import type {
  Todo_skip_id_,
  Todo_skip_value_,
  GetTodoParams,
  Todo,
} from "../types.js";
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
  private readonly todoId: string;
  private readonly userId: string;

  constructor(params: GetTodoParams) {
    this.todoId = params.todoId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetTodoResourceInputs,
    _context: Context,
  ): EagerCollection<Todo_skip_id_, Todo_skip_value_> {
    return inputs.todos.map(
      FilterTodoByIdAndOwnerMapper,
      this.userId,
      this.todoId,
    );
  }
}
