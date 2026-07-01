import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  UserIdKey,
  GroupMember,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each group-member entry, emit one output pair whose key is sourced from the entry's key's userId field and whose value is a GroupMember record listing every required field explicitly: groupId is sourced from the entry's key's groupId field (the original GroupMember.groupId PK component is encoded into the value's groupId field — preserved); userId is sourced from the entry's key's userId field (the original GroupMember.userId PK component is encoded into the new key AND preserved into the value's userId field); addedAt is sourced from the entry's value's addedAt field. The original groupId component of the input key is preserved in the value's groupId field so that downstream consumers of this by-user index can reconstruct the full GroupMember record.
export class GroupMemberByUserFullMapper implements Mapper<
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  UserIdKey,
  GroupMember
> {
  mapEntry(
    key: GroupMember_skip_id_,
    values: Values<GroupMember_skip_value_>,
    context: Context,
  ): Iterable<[UserIdKey, GroupMember]> {
    // > body
    const emits: [UserIdKey, GroupMember][] = [];
    for (const value of values.toArray()) {
      const member: GroupMember = {
        groupId: key.groupId,
        userId: key.userId,
        addedAt: value.addedAt,
      };
      emits.push([key.userId, member]);
    }
    return emits;
    // < body
  }
}
