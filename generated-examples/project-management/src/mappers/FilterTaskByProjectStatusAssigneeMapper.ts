import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Task_skip_id_, Task_skip_value_, Task } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each task entry, emit the entry unchanged when the entry's value's projectId field equals the projectId param AND (the status param is absent OR the entry's value's status field equals the status param) AND (the assigneeId param is absent OR the entry's value's assigneeId field equals the assigneeId param). Otherwise emit nothing.
export class FilterTaskByProjectStatusAssigneeMapper implements Mapper<
  Task_skip_id_,
  Task_skip_value_,
  Task_skip_id_,
  Task_skip_value_
> {
  constructor(
    private projectId: string,
    private status: string | null,
    private assigneeId: string | null,
  ) {}

  mapEntry(
    key: Task_skip_id_,
    values: Values<Task_skip_value_>,
    context: Context,
  ): Iterable<[Task_skip_id_, Task_skip_value_]> {
    // > body
    const emits: [Task_skip_id_, Task_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.projectId !== this.projectId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      if (this.assigneeId !== null && value.assigneeId !== this.assigneeId)
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
