import { FilterLeaderboardByUserMapper } from "../mappers/FilterLeaderboardByUserMapper.js";
import type {
  User_skip_id_,
  LeaderboardRow,
  GetMyLeaderboardEntryParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMyLeaderboardEntryResourceInputs extends SharedCollections {
  readonly leaderboardRows: EagerCollection<User_skip_id_, LeaderboardRow>;
}

export class GetMyLeaderboardEntryResource implements Resource<GetMyLeaderboardEntryResourceInputs> {
  private readonly userId: string;

  constructor(params: GetMyLeaderboardEntryParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMyLeaderboardEntryResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, LeaderboardRow> {
    return inputs.leaderboardRows.map(
      FilterLeaderboardByUserMapper,
      this.userId,
    );
  }
}
