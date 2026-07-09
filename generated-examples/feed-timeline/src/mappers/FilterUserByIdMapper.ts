import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each user entry, emit the entry unchanged when the entry's key equals the userId param. Otherwise emit nothing.
export class FilterUserByIdMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  User_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, User_skip_value_]> {
    // > body
    const emits: [User_skip_id_, User_skip_value_][] = [];
    if (key === this.userId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
