import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  RoleBinding,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each role-binding entry, evaluate four optional predicates: (a) when the resourceId param is present, the entry's value resourceId field must equal it; (b) when the roleId param is present, the entry's value roleId field must equal it; (c) when the userId param is present, the entry's value userId field must be present and equal it; (d) when the groupId param is present, the entry's value groupId field must be present and equal it. Absent params impose no constraint. Emit the entry unchanged when all four predicates hold; emit nothing otherwise.
export class FilterRoleBindingsMapper implements Mapper<
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  RoleBinding_skip_id_,
  RoleBinding_skip_value_
> {
  constructor(
    private resourceId: string | null,
    private roleId: string | null,
    private userId: string | null,
    private groupId: string | null,
  ) {}

  mapEntry(
    key: RoleBinding_skip_id_,
    values: Values<RoleBinding_skip_value_>,
    context: Context,
  ): Iterable<[RoleBinding_skip_id_, RoleBinding_skip_value_]> {
    // > body
    const emits: [RoleBinding_skip_id_, RoleBinding_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.resourceId !== null && value.resourceId !== this.resourceId)
        continue;
      if (this.roleId !== null && value.roleId !== this.roleId) continue;
      if (
        this.userId !== null &&
        (value.userId === undefined || value.userId !== this.userId)
      )
        continue;
      if (
        this.groupId !== null &&
        (value.groupId === undefined || value.groupId !== this.groupId)
      )
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
