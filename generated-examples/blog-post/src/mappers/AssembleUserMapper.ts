import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each user entry, emit one output pair whose key is the entry's key and whose value lists every field of User explicitly: id sourced from the entry's key (required); username present when the entry's value's username field is present, sourced from the entry's value's username field, absent otherwise; displayName present when the entry's value's displayName field is present, sourced from the entry's value's displayName field, absent otherwise; email present when the entry's value's email field is present, sourced from the entry's value's email field, absent otherwise; avatarUrl present when the entry's value's avatarUrl field is present, sourced from the entry's value's avatarUrl field, absent otherwise; bio present when the entry's value's bio field is present, sourced from the entry's value's bio field, absent otherwise; createdAt present when the entry's value's createdAt field is present, sourced from the entry's value's createdAt field, absent otherwise.
export class AssembleUserMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  User
> {
  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, User]> {
    // > body
    const emits: [User_skip_id_, User][] = [];
    for (const value of values.toArray()) {
      const user: User = {
        id: key,
        ...(value.username !== undefined && { username: value.username }),
        ...(value.displayName !== undefined && {
          displayName: value.displayName,
        }),
        ...(value.email !== undefined && { email: value.email }),
        ...(value.avatarUrl !== undefined && { avatarUrl: value.avatarUrl }),
        ...(value.bio !== undefined && { bio: value.bio }),
        ...(value.createdAt !== undefined && { createdAt: value.createdAt }),
      };
      emits.push([key, user]);
    }
    return emits;
    // < body
  }
}
