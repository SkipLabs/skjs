import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  Project,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each project entry, emit the entry unchanged when the entry's key equals the projectId param AND the entry's value's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterProjectByIdAndOwnerMapper implements Mapper<
  Project_skip_id_,
  Project_skip_value_,
  Project_skip_id_,
  Project_skip_value_
> {
  constructor(
    private userId: string,
    private projectId: string,
  ) {}

  mapEntry(
    key: Project_skip_id_,
    values: Values<Project_skip_value_>,
    context: Context,
  ): Iterable<[Project_skip_id_, Project_skip_value_]> {
    // > body
    const emits: [Project_skip_id_, Project_skip_value_][] = [];
    if (key !== this.projectId) return emits;
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
