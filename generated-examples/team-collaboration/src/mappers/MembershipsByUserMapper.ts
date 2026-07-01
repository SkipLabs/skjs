import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  MembershipKey,
  Membership_skip_value_,
  User_skip_id_,
  Membership,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each membership entry, emit one output pair whose key is sourced from the entry's key's userId field (which is the User primary key), paired with a new value listing every required field of Membership explicitly: workspaceId is sourced from the entry's key's workspaceId field, userId is sourced from the entry's key's userId field, role is sourced from the entry's value's role field, joinedAt is sourced from the entry's value's joinedAt field.
export class MembershipsByUserMapper implements Mapper<
  MembershipKey,
  Membership_skip_value_,
  User_skip_id_,
  Membership
> {
  mapEntry(
    key: MembershipKey,
    values: Values<Membership_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Membership]> {
    // > body
    const emits: [User_skip_id_, Membership][] = [];
    for (const value of values.toArray()) {
      const membership: Membership = {
        workspaceId: key.workspaceId,
        userId: key.userId,
        role: value.role,
        joinedAt: value.joinedAt,
      };
      emits.push([key.userId, membership]);
    }
    return emits;
    // < body
  }
}
