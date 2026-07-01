import type { User_skip_id_, LeaderboardRow, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetLeaderboardResourceInputs extends SharedCollections {
  readonly leaderboardRows: EagerCollection<User_skip_id_, LeaderboardRow>;
}

export class GetLeaderboardResource implements Resource<GetLeaderboardResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetLeaderboardResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, LeaderboardRow> {
    return inputs.leaderboardRows;
  }
}
