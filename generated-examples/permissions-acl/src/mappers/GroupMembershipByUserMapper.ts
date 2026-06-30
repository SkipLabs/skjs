import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  User_skip_id_,
  GroupMembershipByUserValue,
  GroupMembership,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each group-membership entry, emit one output pair whose key is sourced from the entry's key userId component, paired with a new value listing every required field of GroupMembershipByUserValue explicitly: groupId sourced from the entry's key groupId component (= the original GroupMembership.groupId), addedAt sourced from the entry's value addedAt field. The original GroupMembership.userId is encoded into the new key. The original GroupMembership.groupId is preserved in the value as groupId so the consumer can reconstruct group ancestry.
export class GroupMembershipByUserMapper implements Mapper<
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  User_skip_id_,
  GroupMembershipByUserValue
> {
  mapEntry(
    key: GroupMembership_skip_id_,
    values: Values<GroupMembership_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, GroupMembershipByUserValue]> {
    // > body
    const emits: [User_skip_id_, GroupMembershipByUserValue][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.userId,
        { groupId: key.groupId, addedAt: value.addedAt },
      ]);
    }
    return emits;
    // < body
  }
}
