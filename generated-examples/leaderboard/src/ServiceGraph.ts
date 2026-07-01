import { AggregateToSortKeyMapper } from "./mappers/AggregateToSortKeyMapper.js";
import { LeaderboardRankMapper } from "./mappers/LeaderboardRankMapper.js";
import { ScoreEntryByOwnerMapper } from "./mappers/ScoreEntryByOwnerMapper.js";
import { ScoreEntryToEpochMsMapper } from "./mappers/ScoreEntryToEpochMsMapper.js";
import { ShuffleAllToZeroMapper } from "./mappers/ShuffleAllToZeroMapper.js";
import { UserAggregateMapper } from "./mappers/UserAggregateMapper.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry,
  ScoreEntry_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  LeaderboardRow,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly scores: EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly leaderboardRows: EagerCollection<User_skip_id_, LeaderboardRow>;
  readonly scores: EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const scoresWithEpochMs = inputs.scores.map(ScoreEntryToEpochMsMapper);
  const scoresByOwner = scoresWithEpochMs.map(ScoreEntryByOwnerMapper);
  const userAggregates = inputs.users.map(UserAggregateMapper, scoresByOwner);
  const aggregatesSorted = userAggregates.map(AggregateToSortKeyMapper);
  const aggregatesUnderZero = aggregatesSorted.map(ShuffleAllToZeroMapper);
  const leaderboardRows = aggregatesUnderZero.map(
    LeaderboardRankMapper,
    inputs.users,
  );
  const output_leaderboardRows = leaderboardRows;
  const output_scores = inputs.scores;
  const output_users = inputs.users;
  return {
    leaderboardRows: output_leaderboardRows,
    scores: output_scores,
    users: output_users,
  };
}
