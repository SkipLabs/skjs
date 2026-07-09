import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Follow_skip_id_,
  Follow_skip_value_,
  User_skip_id_,
  FollowByFollowerValue,
  Follow,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each follow entry, emit one output pair whose key is sourced from the input key's followerId field (which is a User id, matching User_skip_id_), paired with a new value of type FollowByFollowerValue whose followeeId is sourced from the input key's followeeId field and whose createdAt is sourced from the entry's value's createdAt field. This re-injects the followeeId component of the composite primary key on the value side so downstream consumers (feed following-scope filter, FollowsByFollowerResource) can recover which followee each entry references when consulting by followerId.
export class FollowByFollowerMapper implements Mapper<
  Follow_skip_id_,
  Follow_skip_value_,
  User_skip_id_,
  FollowByFollowerValue
> {
  mapEntry(
    key: Follow_skip_id_,
    values: Values<Follow_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, FollowByFollowerValue]> {
    // > body
    const emits: [User_skip_id_, FollowByFollowerValue][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.followerId,
        { followeeId: key.followeeId, createdAt: value.createdAt },
      ]);
    }
    return emits;
    // < body
  }
}
