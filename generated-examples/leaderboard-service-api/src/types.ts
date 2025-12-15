export type ScoreId = string;

export type ScoreValue = {
  userId: string;
  points: number;
  timestamp: number;
};

export type Score = ScoreValue & { id: ScoreId };

export type LeaderboardEntryId = string;

export type LeaderboardEntryValue = {
  userId: string;
  highScore: number;
  rank: number;
};

export type LeaderboardEntry = LeaderboardEntryValue & { id: LeaderboardEntryId };
