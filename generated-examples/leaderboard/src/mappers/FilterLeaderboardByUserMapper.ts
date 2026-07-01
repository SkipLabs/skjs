import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, LeaderboardRow, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each leaderboard row entry, emit the entry unchanged when the entry's key equals the userId param. Otherwise emit nothing.
export class FilterLeaderboardByUserMapper implements Mapper<
  User_skip_id_,
  LeaderboardRow,
  User_skip_id_,
  LeaderboardRow
> {
  constructor(private userId: string) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<LeaderboardRow>,
    context: Context,
  ): Iterable<[User_skip_id_, LeaderboardRow]> {
    // > body
    const emits: [User_skip_id_, LeaderboardRow][] = [];
    if (key === this.userId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
