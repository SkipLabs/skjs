import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, UserStored, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each user entry, emit one output pair whose key is the entry's key, and whose value is a User record listing every required field: id sourced from the entry's key. Optional fields: displayName is present when the entry's value's displayName field is present, sourced from it; absent otherwise. email is present when the entry's value's email field is present, sourced from it; absent otherwise. companyName is present when the entry's value's companyName field is present, sourced from it; absent otherwise. companyAddress is present when the entry's value's companyAddress field is present, sourced from it; absent otherwise.
export class AssembleUserMapper implements Mapper<
  User_skip_id_,
  UserStored,
  User_skip_id_,
  User
> {
  mapEntry(
    key: User_skip_id_,
    values: Values<UserStored>,
    context: Context,
  ): Iterable<[User_skip_id_, User]> {
    // > body
    const emits: [User_skip_id_, User][] = [];
    for (const value of values.toArray()) {
      const user: User = {
        id: key,
        ...(value.displayName !== undefined && {
          displayName: value.displayName,
        }),
        ...(value.email !== undefined && { email: value.email }),
        ...(value.companyName !== undefined && {
          companyName: value.companyName,
        }),
        ...(value.companyAddress !== undefined && {
          companyAddress: value.companyAddress,
        }),
      };
      emits.push([key, user]);
    }
    return emits;
    // < body
  }
}
