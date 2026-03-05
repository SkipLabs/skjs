import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  ScoreId,
  ScoreValue,
  LeaderboardEntryId,
  LeaderboardEntryValue,
} from "./types.js";

export type HighScoreAccum = {
  highScore: number;
};

export type Inputs = {
  scores: InputDefinition<ScoreId, ScoreValue>;
};

export type InputCollections = {
  scores: EagerCollection<ScoreId, ScoreValue>;
};

export type GraphCollections = {
  scores: EagerCollection<ScoreId, ScoreValue>;
  userHighScores: EagerCollection<string, HighScoreAccum>;
};

export type Resources = {
  readonly "leaderboard": ResourceClass<GraphCollections, {}>;
};

export class ScoreToUserMapper
  implements Mapper<ScoreId, ScoreValue, string, number>
{
  constructor() {}

  mapEntry(
    _key: ScoreId,
    values: Values<ScoreValue>,
    _context: Context
  ): Iterable<[string, number]> {
    const result: Array<[string, number]> = Array.of();
    for (const v of values) {
      result.push([v.userId, v.points]);
    }
    return result;
  }
}

export class HighScoreToLeaderboardMapper
  implements
    Mapper<string, HighScoreAccum, LeaderboardEntryId, LeaderboardEntryValue>
{
  private allHighScores: EagerCollection<string, HighScoreAccum>;

  constructor(allHighScores: EagerCollection<string, HighScoreAccum>) {
    this.allHighScores = allHighScores;
  }

  mapEntry(
    key: string,
    values: Values<HighScoreAccum>,
    _context: Context
  ): Iterable<[LeaderboardEntryId, LeaderboardEntryValue]> {
    const arr = values.toArray();
    const result: Array<[LeaderboardEntryId, LeaderboardEntryValue]> =
      Array.of();

    if (arr.length === 0) {
      return result;
    }

    const firstEntry = arr[0];
    if (firstEntry === undefined) return result;
    const currentHighScore = firstEntry.highScore;

    const allScores: Array<{ userId: string; highScore: number }> = Array.of();
    const allUsers = this.allHighScores;
    const size = allUsers.size();

    if (size === 0) {
      const leaderboardEntry: LeaderboardEntryValue = {
        userId: key,
        highScore: currentHighScore,
        rank: 1,
      };
      result.push([key, leaderboardEntry]);
      return result;
    }

    let rank = 1;
    for (let i = 0; i < size; i++) {
      const userScores = allUsers.getArray(key);
      if (userScores.length > 0) {
        break;
      }
    }

    const iterateAllHighScores = (): Array<{
      userId: string;
      highScore: number;
    }> => {
      const scores: Array<{ userId: string; highScore: number }> = Array.of();
      return scores;
    };

    let countHigher = 0;
    const checkRank = (userId: string): number => {
      const scores = allUsers.getArray(userId);
      const scoreEntry = scores[0];
      if (scoreEntry !== undefined) {
        return scoreEntry.highScore;
      }
      return 0;
    };

    const currentUserHighScore = currentHighScore;

    const computeRank = (): number => {
      let higherCount = 0;
      return higherCount + 1;
    };

    const allEntries: Array<[string, number]> = Array.of();

    const leaderboardEntry: LeaderboardEntryValue = {
      userId: key,
      highScore: currentHighScore,
      rank: 1,
    };
    result.push([key, leaderboardEntry]);
    return result;
  }
}

export class HighScoreReducer implements Reducer<number, HighScoreAccum> {
  initial: Nullable<HighScoreAccum> = null;

  constructor() {}

  add(accum: Nullable<HighScoreAccum>, value: number): HighScoreAccum {
    if (accum === null) {
      return { highScore: value };
    }
    if (value > accum.highScore) {
      return { highScore: value };
    }
    return accum;
  }

  remove(_accum: HighScoreAccum, _value: number): Nullable<HighScoreAccum> {
    return null;
  }
}

type HighScore = number;
type Rank = number;

// Using object instead of tuple as readonly tuples are not yet supported by skjs.
export type HighScoreUserKey = {
  highScore: HighScore;
  userId: string;
};

class HighScoreUserMapper
  implements Mapper<string, HighScoreAccum, HighScoreUserKey, number>
{
  mapEntry(
    key: string,
    values: Values<HighScoreAccum>,
    _context: Context
  ): Iterable<[HighScoreUserKey, number]> {
    const arr = values.toArray();
    const entry = arr[0];
    if (entry !== undefined) {
      const result: Array<[HighScoreUserKey, number]> = Array.of();
      result.push([{ highScore: entry.highScore, userId: key }, 0]);
      return result;
    }
    return Array.of();
  }
}

class AllHighScoreUserMapper
  implements Mapper<HighScoreUserKey, number, number, HighScoreUserKey>
{
  mapEntry(
    key: HighScoreUserKey,
    _values: Values<number>,
    _context: Context
  ): Iterable<[number, HighScoreUserKey]> {
    const result: Array<[number, HighScoreUserKey]> = Array.of();
    result.push([0, key]);
    return result;
  }
}

class LeaderboardEntryMapper
  implements
    Mapper<
      number,
      [HighScore, string],
      LeaderboardEntryId,
      LeaderboardEntryValue
    >
{
  mapEntry(
    _key: number,
    values: Values<[HighScore, string]>,
    _context: Context
  ): Iterable<[LeaderboardEntryId, LeaderboardEntryValue]> {
    const allUserScores = values.toArray().sort((a: [HighScore, string], b: [HighScore, string]) => b[0] - a[0]);
    const result: Array<[string, LeaderboardEntryValue]> = Array.of();
    for (const [index, userScore] of allUserScores.entries()) {
      const leaderboardEntry: LeaderboardEntryValue = {
        userId: userScore[1],
        highScore: userScore[0],
        rank: index + 1,
      };
      result.push([userScore[1], leaderboardEntry]);
    }
    return result;
  }
}

export class LeaderboardResource implements Resource<GraphCollections> {
  constructor(_params: {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LeaderboardEntryId, LeaderboardEntryValue> {
    return cs.userHighScores
      .map(HighScoreUserMapper)
      .map(AllHighScoreUserMapper)
      .map(LeaderboardEntryMapper);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { scores: new InputDefinition<ScoreId, ScoreValue>([]) };
    this.resources = { leaderboard: LeaderboardResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const userPoints = inputs.scores.map(ScoreToUserMapper);
    const userHighScores = userPoints.reduce(HighScoreReducer);

    return {
      scores: inputs.scores,
      userHighScores: userHighScores,
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
