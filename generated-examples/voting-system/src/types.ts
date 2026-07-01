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

export type CastVoteRequest = { readonly optionId: string } & {
  readonly [key: string]: Json | null;
};

export type CastVoteRequest_skip_id_ = { readonly optionId: string } & {
  readonly [key: string]: Json | null;
};

export type CastVoteRequest_skip_value_ = { readonly optionId: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePollOptionRequest = { readonly label: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePollOptionRequest_skip_id_ = { readonly label: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePollOptionRequest_skip_value_ = { readonly label: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePollRequest = {
  readonly options: CreatePollOptionRequest[];
  readonly question: string;
} & { readonly [key: string]: Json | null };

export type CreatePollRequest_skip_id_ = {
  readonly options: CreatePollOptionRequest[];
  readonly question: string;
} & { readonly [key: string]: Json | null };

export type CreatePollRequest_skip_value_ = {
  readonly options: CreatePollOptionRequest[];
  readonly question: string;
} & { readonly [key: string]: Json | null };

export type GetPollParams = { readonly pollId: string } & {
  readonly [key: string]: Json | null;
};

export type GetPollVoteParams = {
  readonly pollId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListPollVotesParams = { readonly pollId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPollsParams = { readonly status: PollStatus } & {
  readonly [key: string]: Json | null;
};

export type Poll = {
  readonly closedAt?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly options: PollOption[];
  readonly ownerId: string;
  readonly question: string;
  readonly status: PollStatus;
  readonly totalVotes: number;
} & { readonly [key: string]: Json | null };

export type PollList = { readonly items: Poll[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type PollList_skip_id_ = {
  readonly items: Poll[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PollList_skip_value_ = {
  readonly items: Poll[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PollOption = {
  readonly label: string;
  readonly optionId: string;
  readonly pollId: string;
  readonly voteCount: number;
} & { readonly [key: string]: Json | null };

export type PollOptionKey = {
  readonly optionId: string;
  readonly pollId: string;
} & { readonly [key: string]: Json | null };

export type PollOptionStored = { readonly label: string } & {
  readonly [key: string]: Json | null;
};

export type PollOption_skip_id_ = {
  readonly optionId: string;
  readonly pollId: string;
} & { readonly [key: string]: Json | null };

export type PollOption_skip_value_ = {
  readonly label: string;
  readonly voteCount: number;
} & { readonly [key: string]: Json | null };

export type PollStatus = "OPEN" | "CLOSED";

export type PollStatus_skip_id_ = "OPEN" | "CLOSED";

export type PollStatus_skip_value_ = "OPEN" | "CLOSED";

export type PollStored = {
  readonly closedAt?: string;
  readonly createdAt: string;
  readonly ownerId: string;
  readonly question: string;
  readonly status: PollStatus;
} & { readonly [key: string]: Json | null };

export type Poll_skip_id_ = string;

export type Poll_skip_value_ = {
  readonly closedAt?: string;
  readonly createdAt: string;
  readonly options: PollOption[];
  readonly ownerId: string;
  readonly question: string;
  readonly status: PollStatus;
  readonly totalVotes: number;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePollRequest = {
  readonly question?: string;
  readonly status?: PollStatus;
} & { readonly [key: string]: Json | null };

export type UpdatePollRequest_skip_id_ = {
  readonly question?: string;
  readonly status?: PollStatus;
} & { readonly [key: string]: Json | null };

export type UpdatePollRequest_skip_value_ = {
  readonly question?: string;
  readonly status?: PollStatus;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type Vote = {
  readonly castAt: string;
  readonly optionId: string;
  readonly pollId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type VoteCountValue = number;

export type VoteKey = { readonly pollId: string; readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type VoteList = { readonly items: Vote[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type VoteList_skip_id_ = {
  readonly items: Vote[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type VoteList_skip_value_ = {
  readonly items: Vote[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type VoteStored = {
  readonly castAt: string;
  readonly optionId: string;
} & { readonly [key: string]: Json | null };

export type Vote_skip_id_ = {
  readonly pollId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Vote_skip_value_ = {
  readonly castAt: string;
  readonly optionId: string;
} & { readonly [key: string]: Json | null };
