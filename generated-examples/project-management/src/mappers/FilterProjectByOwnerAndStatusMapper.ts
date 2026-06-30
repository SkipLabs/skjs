import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  Project,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each project entry, emit the entry unchanged when the entry's value's ownerId field equals the userId param AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterProjectByOwnerAndStatusMapper implements Mapper<
  Project_skip_id_,
  Project_skip_value_,
  Project_skip_id_,
  Project_skip_value_
> {
  constructor(
    private userId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: Project_skip_id_,
    values: Values<Project_skip_value_>,
    context: Context,
  ): Iterable<[Project_skip_id_, Project_skip_value_]> {
    // > body
    const emits: [Project_skip_id_, Project_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
