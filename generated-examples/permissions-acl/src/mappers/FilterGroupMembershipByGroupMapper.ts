import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Group_skip_id_,
  GroupMembershipByGroupValue,
  Group,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the groupId key: when the entry's key does not equal the groupId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key and whose value is the iterated value. The input collection accumulates all memberships for the same group under one key — singleton-only access would raise on any group with 2+ members.
export class FilterGroupMembershipByGroupMapper implements Mapper<
  Group_skip_id_,
  GroupMembershipByGroupValue,
  Group_skip_id_,
  GroupMembershipByGroupValue
> {
  constructor(private groupId: string) {}

  mapEntry(
    key: Group_skip_id_,
    values: Values<GroupMembershipByGroupValue>,
    context: Context,
  ): Iterable<[Group_skip_id_, GroupMembershipByGroupValue]> {
    // > body
    if (key !== this.groupId) return [];
    const emits: [Group_skip_id_, GroupMembershipByGroupValue][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
