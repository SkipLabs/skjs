import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  UserAggregate,
  User_skip_id_,
  LeaderboardRow,
  User_skip_value_,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each entry (there is at most one such invocation under the literal-zero key), receive all UserAggregate values associated with the constant key. Sort the values in the following order: first by totalPoints descending (higher score wins), then by lastSubmittedAtMs ascending (earlier last-submission wins ties), then by userId ascending (final stable tiebreaker). In sorted order, for each value at position i (one-based), consult usersById for the user records indexed by the value's userId field; take the first user record if any is returned, otherwise treat the user record as absent. Emit one output pair whose key is sourced from the value's userId field and whose value lists every required field of LeaderboardRow explicitly: userId sourced from the value's userId field; rank set to the one-based position i; totalPoints sourced from the value's totalPoints field; entryCount sourced from the value's entryCount field; lastSubmittedAtMs sourced from the value's lastSubmittedAtMs field unchanged (numeric epoch milliseconds — the api method formats this to an ISO 8601 date-time string at response time). The optional displayName field is present when the consulted user record has a displayName field, sourced from that field; absent otherwise.
export class LeaderboardRankMapper implements Mapper<
  0,
  UserAggregate,
  User_skip_id_,
  LeaderboardRow
> {
  constructor(
    private usersById: EagerCollection<User_skip_id_, User_skip_value_>,
  ) {}

  mapEntry(
    key: 0,
    values: Values<UserAggregate>,
    context: Context,
  ): Iterable<[User_skip_id_, LeaderboardRow]> {
    // > body
    const arr = values.toArray();
    const sorted = arr.slice().sort((a, b) => {
      if (a.totalPoints !== b.totalPoints) return b.totalPoints - a.totalPoints;
      if (a.lastSubmittedAtMs !== b.lastSubmittedAtMs)
        return a.lastSubmittedAtMs - b.lastSubmittedAtMs;
      if (a.userId < b.userId) return -1;
      if (a.userId > b.userId) return 1;
      return 0;
    });
    const emits: [User_skip_id_, LeaderboardRow][] = [];
    for (let i = 0; i < sorted.length; i++) {
      const value = sorted[i];
      if (value === undefined) throw new Error("Expected value");
      const rank = i + 1;
      const userRecord = this.usersById.getArray(value.userId)[0];
      const row: LeaderboardRow = {
        userId: value.userId,
        rank,
        totalPoints: value.totalPoints,
        entryCount: value.entryCount,
        lastSubmittedAtMs: value.lastSubmittedAtMs,
        ...(userRecord !== undefined &&
          userRecord.displayName !== undefined && {
            displayName: userRecord.displayName,
          }),
      };
      emits.push([value.userId, row]);
    }
    return emits;
    // < body
  }
}
