import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  UserAggregate,
  LeaderboardSortKey,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each aggregate entry, emit one output pair whose key is a LeaderboardSortKey lifted from the entry's value: negTotalPoints is the negation of the value's totalPoints field (so ascending key order produces descending totalPoints); lastSubmittedAtMs is sourced from the value's lastSubmittedAtMs field; userId is sourced from the value's userId field. The value is the entry's value unchanged. The original user id from the input key is preserved via the value's userId field, so consumers can still reconstruct the user.
export class AggregateToSortKeyMapper implements Mapper<
  User_skip_id_,
  UserAggregate,
  LeaderboardSortKey,
  UserAggregate
> {
  mapEntry(
    key: User_skip_id_,
    values: Values<UserAggregate>,
    context: Context,
  ): Iterable<[LeaderboardSortKey, UserAggregate]> {
    // > body
    const emits: [LeaderboardSortKey, UserAggregate][] = [];
    for (const value of values.toArray()) {
      const sortKey: LeaderboardSortKey = {
        negTotalPoints: -value.totalPoints,
        lastSubmittedAtMs: value.lastSubmittedAtMs,
        userId: value.userId,
      };
      emits.push([sortKey, value]);
    }
    return emits;
    // < body
  }
}
