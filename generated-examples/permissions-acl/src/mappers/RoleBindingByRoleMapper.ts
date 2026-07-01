import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  Role_skip_id_,
  RoleBindingByRoleValue,
  RoleBinding,
  Role,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each role-binding entry, emit one output pair whose key is sourced from the entry's value roleId field, paired with a new value listing every required field of RoleBindingByRoleValue explicitly: id sourced from the entry's key (= the original RoleBinding.id, preserved in the value), roleId sourced from the entry's value roleId field, resourceId sourced from the entry's value resourceId field, userId sourced from the entry's value userId field when present (otherwise absent), groupId sourced from the entry's value groupId field when present (otherwise absent), createdBy sourced from the entry's value createdBy field, createdAt sourced from the entry's value createdAt field. The original RoleBinding.id is preserved in the value as id.
export class RoleBindingByRoleMapper implements Mapper<
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  Role_skip_id_,
  RoleBindingByRoleValue
> {
  mapEntry(
    key: RoleBinding_skip_id_,
    values: Values<RoleBinding_skip_value_>,
    context: Context,
  ): Iterable<[Role_skip_id_, RoleBindingByRoleValue]> {
    // > body
    const emits: [Role_skip_id_, RoleBindingByRoleValue][] = [];
    for (const value of values.toArray()) {
      const out: RoleBindingByRoleValue = {
        id: key,
        roleId: value.roleId,
        resourceId: value.resourceId,
        ...(value.userId !== undefined && { userId: value.userId }),
        ...(value.groupId !== undefined && { groupId: value.groupId }),
        createdBy: value.createdBy,
        createdAt: value.createdAt,
      };
      emits.push([value.roleId, out]);
    }
    return emits;
    // < body
  }
}
