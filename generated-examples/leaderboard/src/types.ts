import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code?: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type GetMyLeaderboardEntryParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Leaderboard = { readonly rows: LeaderboardEntry[] } & {
  readonly [key: string]: Json | null;
};

export type LeaderboardEntry = {
  readonly displayName?: string;
  readonly entryCount: number;
  readonly lastSubmittedAt: string;
  readonly rank: number;
  readonly totalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type LeaderboardEntry_skip_id_ = {
  readonly displayName?: string;
  readonly entryCount: number;
  readonly lastSubmittedAt: string;
  readonly rank: number;
  readonly totalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type LeaderboardEntry_skip_value_ = {
  readonly displayName?: string;
  readonly entryCount: number;
  readonly lastSubmittedAt: string;
  readonly rank: number;
  readonly totalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type LeaderboardRow = {
  readonly displayName?: string;
  readonly entryCount: number;
  readonly lastSubmittedAtMs: number;
  readonly rank: number;
  readonly totalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type LeaderboardSortKey = {
  readonly lastSubmittedAtMs: number;
  readonly negTotalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Leaderboard_skip_id_ = { readonly rows: LeaderboardEntry[] } & {
  readonly [key: string]: Json | null;
};

export type Leaderboard_skip_value_ = { readonly rows: LeaderboardEntry[] } & {
  readonly [key: string]: Json | null;
};

export type ListScoresParams = { readonly userId?: string } & {
  readonly [key: string]: Json | null;
};

export type ScoreEntry = {
  readonly id: string;
  readonly ownerUserId: string;
  readonly points: number;
  readonly reason?: string;
  readonly submittedAt: string;
} & { readonly [key: string]: Json | null };

export type ScoreEntryList = { readonly entries: ScoreEntry[] } & {
  readonly [key: string]: Json | null;
};

export type ScoreEntryList_skip_id_ = { readonly entries: ScoreEntry[] } & {
  readonly [key: string]: Json | null;
};

export type ScoreEntryList_skip_value_ = { readonly entries: ScoreEntry[] } & {
  readonly [key: string]: Json | null;
};

export type ScoreEntryWithEpochMs = {
  readonly id: string;
  readonly ownerUserId: string;
  readonly points: number;
  readonly reason?: string;
  readonly submittedAtMs: number;
} & { readonly [key: string]: Json | null };

export type ScoreEntry_skip_id_ = string;

export type ScoreEntry_skip_value_ = {
  readonly ownerUserId: string;
  readonly points: number;
  readonly reason?: string;
  readonly submittedAt: string;
} & { readonly [key: string]: Json | null };

export type SubmitScoreRequest = {
  readonly points: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type SubmitScoreRequest_skip_id_ = {
  readonly points: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type SubmitScoreRequest_skip_value_ = {
  readonly points: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type UserAggregate = {
  readonly entryCount: number;
  readonly lastSubmittedAtMs: number;
  readonly totalPoints: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };
