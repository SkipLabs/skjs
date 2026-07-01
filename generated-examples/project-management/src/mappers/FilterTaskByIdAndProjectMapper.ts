import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Task_skip_id_, Task_skip_value_, Task } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each task entry, emit the entry unchanged when the entry's key equals the taskId param AND the entry's value's projectId field equals the projectId param. Otherwise emit nothing.
export class FilterTaskByIdAndProjectMapper implements Mapper<
  Task_skip_id_,
  Task_skip_value_,
  Task_skip_id_,
  Task_skip_value_
> {
  constructor(
    private projectId: string,
    private taskId: string,
  ) {}

  mapEntry(
    key: Task_skip_id_,
    values: Values<Task_skip_value_>,
    context: Context,
  ): Iterable<[Task_skip_id_, Task_skip_value_]> {
    // > body
    if (key !== this.taskId) return [];
    const emits: [Task_skip_id_, Task_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.projectId === this.projectId) emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
