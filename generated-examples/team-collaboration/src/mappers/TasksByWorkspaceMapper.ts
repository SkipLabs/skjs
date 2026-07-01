import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Task_skip_id_,
  Task_skip_value_,
  Workspace_skip_id_,
  Task,
  Workspace,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each task entry, emit one output pair whose key is sourced from the entry's value's workspaceId field (which is the Workspace primary key), paired with a new value listing every required field of Task explicitly: id is sourced from the entry's key, workspaceId is sourced from the entry's value's workspaceId field, title is sourced from the entry's value's title field, description is sourced from the entry's value's description field, status is sourced from the entry's value's status field, assigneeId is sourced from the entry's value's assigneeId field, createdById is sourced from the entry's value's createdById field, dueAt is sourced from the entry's value's dueAt field, createdAt is sourced from the entry's value's createdAt field, updatedAt is sourced from the entry's value's updatedAt field.
export class TasksByWorkspaceMapper implements Mapper<
  Task_skip_id_,
  Task_skip_value_,
  Workspace_skip_id_,
  Task
> {
  mapEntry(
    key: Task_skip_id_,
    values: Values<Task_skip_value_>,
    context: Context,
  ): Iterable<[Workspace_skip_id_, Task]> {
    // > body
    const emits: [Workspace_skip_id_, Task][] = [];
    for (const value of values.toArray()) {
      const task: Task = {
        id: key,
        workspaceId: value.workspaceId,
        title: value.title,
        status: value.status,
        createdById: value.createdById,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
        ...(value.assigneeId !== undefined && { assigneeId: value.assigneeId }),
        ...(value.dueAt !== undefined && { dueAt: value.dueAt }),
      };
      emits.push([value.workspaceId, task]);
    }
    return emits;
    // < body
  }
}
