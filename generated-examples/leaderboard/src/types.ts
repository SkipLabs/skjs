export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Board = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly scoringMode: ScoringMode;
  readonly updatedAt?: string;
};

export type BoardList = { readonly boards: Board[]; readonly total?: number };

export type BoardList_skip_id_ = {
  readonly boards: Board[];
  readonly total?: number;
};

export type BoardList_skip_value_ = {
  readonly boards: Board[];
  readonly total?: number;
};

export type Board_skip_id_ = string;

export type Board_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly scoringMode: ScoringMode;
  readonly updatedAt?: string;
};

export type CreateBoardRequest = {
  readonly description?: string;
  readonly name: string;
  readonly scoringMode: ScoringMode;
};

export type CreateBoardRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly scoringMode: ScoringMode;
};

export type CreateBoardRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly scoringMode: ScoringMode;
};

export type GetBoardParams = { readonly boardId: string };

export type GetBoardRankingsParams = { readonly boardId: string };

export type GetMeParams = { readonly userId: string };

export type GetScoreEntryParams = { readonly entryId: string };

export type GetUserByIdParams = { readonly userId: string };

export type ListBoardEntriesParams = {
  readonly boardId: string;
  readonly userId?: string;
};

export type Ranking = {
  readonly boardId: string;
  readonly rows: RankingRow[];
  readonly scoringMode: ScoringMode;
  readonly totalUsers?: number;
};

export type RankingRow = {
  readonly entryCount: number;
  readonly lastEntryAt?: string;
  readonly rank: number;
  readonly totalScore: number;
  readonly userId: string;
};

export type RankingRow_skip_id_ = {
  readonly entryCount: number;
  readonly lastEntryAt?: string;
  readonly rank: number;
  readonly totalScore: number;
  readonly userId: string;
};

export type RankingRow_skip_value_ = {
  readonly entryCount: number;
  readonly lastEntryAt?: string;
  readonly rank: number;
  readonly totalScore: number;
  readonly userId: string;
};

export type Ranking_skip_id_ = {
  readonly boardId: string;
  readonly rows: RankingRow[];
  readonly scoringMode: ScoringMode;
  readonly totalUsers?: number;
};

export type Ranking_skip_value_ = {
  readonly boardId: string;
  readonly rows: RankingRow[];
  readonly scoringMode: ScoringMode;
  readonly totalUsers?: number;
};

export type ScoreEntry = {
  readonly boardId: string;
  readonly createdAt: string;
  readonly id: string;
  readonly note?: string;
  readonly points: number;
  readonly userId: string;
};

export type ScoreEntryList = {
  readonly entries: ScoreEntry[];
  readonly total?: number;
};

export type ScoreEntryList_skip_id_ = {
  readonly entries: ScoreEntry[];
  readonly total?: number;
};

export type ScoreEntryList_skip_value_ = {
  readonly entries: ScoreEntry[];
  readonly total?: number;
};

export type ScoreEntry_skip_id_ = string;

export type ScoreEntry_skip_value_ = {
  readonly boardId: string;
  readonly createdAt: string;
  readonly note?: string;
  readonly points: number;
  readonly userId: string;
};

export type ScoringMode = "SUM" | "MAX" | "LATEST";

export type ScoringMode_skip_id_ = "SUM" | "MAX" | "LATEST";

export type ScoringMode_skip_value_ = "SUM" | "MAX" | "LATEST";

export type SubmitScoreEntryRequest = {
  readonly note?: string;
  readonly points: number;
};

export type SubmitScoreEntryRequest_skip_id_ = {
  readonly note?: string;
  readonly points: number;
};

export type SubmitScoreEntryRequest_skip_value_ = {
  readonly note?: string;
  readonly points: number;
};

export type UpdateBoardRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly scoringMode?: ScoringMode;
};

export type UpdateBoardRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly scoringMode?: ScoringMode;
};

export type UpdateBoardRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly scoringMode?: ScoringMode;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
};
