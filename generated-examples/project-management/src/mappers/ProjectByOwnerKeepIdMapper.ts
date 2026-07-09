import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  User_skip_id_,
  Project,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each project entry, when the entry's value ownerId field does not equal the userId param, emit nothing. Otherwise emit one output pair whose key is sourced from the userId param and whose value lists every required field of Project explicitly: id sourced from the entry's key; ownerId sourced from the entry's value ownerId field; name sourced from the entry's value name field; status sourced from the entry's value status field; createdAt sourced from the entry's value createdAt field; updatedAt sourced from the entry's value updatedAt field. Optional field description: present when the entry's value description field is present, sourced from the entry's value description field; absent otherwise.
export class ProjectByOwnerKeepIdMapper implements Mapper<
  Project_skip_id_,
  Project_skip_value_,
  User_skip_id_,
  Project
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Project_skip_id_,
    values: Values<Project_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Project]> {
    // > body
    const emits: [User_skip_id_, Project][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      const project: Project = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        status: value.status,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([this.userId, project]);
    }
    return emits;
    // < body
  }
}
