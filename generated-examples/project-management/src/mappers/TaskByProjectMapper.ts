import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  Project_skip_id_,
  Task,
  Project,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each task entry, when the entry's value projectId field does not equal the projectId param, emit nothing. Otherwise emit one output pair whose key is sourced from the projectId param and whose value lists every required field of Task explicitly: id sourced from the entry's key; projectId sourced from the entry's value projectId field; createdBy sourced from the entry's value createdBy field; title sourced from the entry's value title field; status sourced from the entry's value status field; priority sourced from the entry's value priority field; createdAt sourced from the entry's value createdAt field; updatedAt sourced from the entry's value updatedAt field. Optional fields — assigneeId: present when the entry's value assigneeId field is present, sourced from that field; absent otherwise. description: present when the entry's value description field is present, sourced from that field; absent otherwise. dueDate: present when the entry's value dueDate field is present, sourced from that field; absent otherwise. completedAt: present when the entry's value completedAt field is present, sourced from that field; absent otherwise.
export class TaskByProjectMapper implements Mapper<
  Task_skip_id_,
  Task_skip_value_,
  Project_skip_id_,
  Task
> {
  constructor(private projectId: string) {}

  mapEntry(
    key: Task_skip_id_,
    values: Values<Task_skip_value_>,
    context: Context,
  ): Iterable<[Project_skip_id_, Task]> {
    // > body
    const emits: [Project_skip_id_, Task][] = [];
    for (const value of values.toArray()) {
      if (value.projectId !== this.projectId) continue;
      const task: Task = {
        id: key,
        projectId: value.projectId,
        createdBy: value.createdBy,
        title: value.title,
        status: value.status,
        priority: value.priority,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.assigneeId !== undefined && { assigneeId: value.assigneeId }),
        ...(value.description !== undefined && {
          description: value.description,
        }),
        ...(value.dueDate !== undefined && { dueDate: value.dueDate }),
        ...(value.completedAt !== undefined && {
          completedAt: value.completedAt,
        }),
      };
      emits.push([this.projectId, task]);
    }
    return emits;
    // < body
  }
}
