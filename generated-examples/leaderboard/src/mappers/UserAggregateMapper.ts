import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  UserAggregate,
  ScoreEntryWithEpochMs,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, consult scoresByOwner for the score entry values indexed by the entry's key. When no values are consulted (the user has no score entries), emit nothing (users with zero entries are excluded from the leaderboard). Otherwise, compute: totalPoints as the sum of the consulted values' points fields; entryCount as the count of consulted values; lastSubmittedAtMs as the maximum of the consulted values' submittedAtMs fields (already numeric epoch milliseconds — no parsing, no formatting). Emit one output pair whose key is the entry's key and whose value lists every required field of UserAggregate explicitly: userId sourced from the entry's key; totalPoints, entryCount, lastSubmittedAtMs computed as described.
export class UserAggregateMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  UserAggregate
> {
  constructor(
    private scoresByOwner: EagerCollection<
      User_skip_id_,
      ScoreEntryWithEpochMs
    >,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, UserAggregate]> {
    // > body
    const entries: ScoreEntryWithEpochMs[] = this.scoresByOwner.getArray(key);
    if (entries.length === 0) return [];
    let totalPoints = 0;
    let entryCount = 0;
    let lastSubmittedAtMs = Number.NEGATIVE_INFINITY;
    for (const entry of entries) {
      totalPoints += entry.points;
      entryCount += 1;
      if (entry.submittedAtMs > lastSubmittedAtMs)
        lastSubmittedAtMs = entry.submittedAtMs;
    }
    const aggregate: UserAggregate = {
      userId: key,
      totalPoints,
      entryCount,
      lastSubmittedAtMs,
    };
    return [[key, aggregate]];
    // < body
  }
}
