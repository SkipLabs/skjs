import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each user entry, when the entry's key does not equal the userId param, emit nothing. Otherwise emit one output pair whose key is the literal zero and whose value lists every required field of User explicitly — id sourced from the entry's key; and every optional field with an explicit presence clause: displayName present when the entry's value carries a displayName field, sourced from the entry's value's displayName field, absent otherwise; email present when the entry's value carries an email field, sourced from the entry's value's email field, absent otherwise; avatarUrl present when the entry's value carries an avatarUrl field, sourced from the entry's value's avatarUrl field, absent otherwise; createdAt present when the entry's value carries a createdAt field, sourced from the entry's value's createdAt field, absent otherwise.
export class GetUserByIdMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  0,
  User
> {
  constructor(private userId: string) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[0, User]> {
    // > body
    if (key !== this.userId) return [];
    const emits: [0, User][] = [];
    for (const value of values.toArray()) {
      const user: User = {
        id: key,
        ...(value.displayName !== undefined && {
          displayName: value.displayName,
        }),
        ...(value.email !== undefined && { email: value.email }),
        ...(value.avatarUrl !== undefined && { avatarUrl: value.avatarUrl }),
        ...(value.createdAt !== undefined && { createdAt: value.createdAt }),
      };
      emits.push([0, user]);
    }
    return emits;
    // < body
  }
}
