import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  GroupIdKey,
  GroupMember,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each group-member entry, emit one output pair whose key is sourced from the entry's key's groupId field and whose value is a GroupMember record listing every required field explicitly: groupId is sourced from the entry's key's groupId field (the original GroupMember.groupId PK component is encoded into the new key AND preserved into the value's groupId field); userId is sourced from the entry's key's userId field (the original GroupMember.userId PK component is preserved into the value's userId field); addedAt is sourced from the entry's value's addedAt field. The original userId component of the input key is preserved in the value's userId field so consumers can reconstruct the full GroupMember record.
export class GroupMemberByGroupMapper implements Mapper<
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  GroupIdKey,
  GroupMember
> {
  mapEntry(
    key: GroupMember_skip_id_,
    values: Values<GroupMember_skip_value_>,
    context: Context,
  ): Iterable<[GroupIdKey, GroupMember]> {
    // > body
    const emits: [GroupIdKey, GroupMember][] = [];
    for (const value of values.toArray()) {
      const member: GroupMember = {
        groupId: key.groupId,
        userId: key.userId,
        addedAt: value.addedAt,
      };
      emits.push([key.groupId, member]);
    }
    return emits;
    // < body
  }
}
