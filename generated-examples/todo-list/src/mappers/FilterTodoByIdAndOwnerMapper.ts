import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Todo_skip_id_, Todo_skip_value_, Todo } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each todo entry, emit the entry unchanged when the entry's key equals the todoId param AND the entry's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterTodoByIdAndOwnerMapper implements Mapper<
  Todo_skip_id_,
  Todo_skip_value_,
  Todo_skip_id_,
  Todo_skip_value_
> {
  constructor(
    private userId: string,
    private todoId: string,
  ) {}

  mapEntry(
    key: Todo_skip_id_,
    values: Values<Todo_skip_value_>,
    context: Context,
  ): Iterable<[Todo_skip_id_, Todo_skip_value_]> {
    // > body
    if (key !== this.todoId) return [];
    const emits: [Todo_skip_id_, Todo_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
