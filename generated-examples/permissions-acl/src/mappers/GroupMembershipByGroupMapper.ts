import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  Group_skip_id_,
  GroupMembershipByGroupValue,
  GroupMembership,
  Group,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each group-membership entry, emit one output pair whose key is sourced from the entry's key groupId component, paired with a new value listing every required field of GroupMembershipByGroupValue explicitly: userId sourced from the entry's key userId component (= the original GroupMembership.userId), addedAt sourced from the entry's value addedAt field. The original GroupMembership.groupId is encoded into the new key. The original GroupMembership.userId is preserved in the value as userId so the consumer can reconstruct the full membership tuple.
export class GroupMembershipByGroupMapper implements Mapper<
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  Group_skip_id_,
  GroupMembershipByGroupValue
> {
  mapEntry(
    key: GroupMembership_skip_id_,
    values: Values<GroupMembership_skip_value_>,
    context: Context,
  ): Iterable<[Group_skip_id_, GroupMembershipByGroupValue]> {
    // > body
    const emits: [Group_skip_id_, GroupMembershipByGroupValue][] = [];
    for (const value of values.toArray()) {
      emits.push([key.groupId, { userId: key.userId, addedAt: value.addedAt }]);
    }
    return emits;
    // < body
  }
}
