export type ApiError = { readonly error: string; readonly message?: string };

export type ApiError_skip_id_ = {
  readonly error: string;
  readonly message?: string;
};

export type ApiError_skip_value_ = {
  readonly error: string;
  readonly message?: string;
};

export type CastVoteRequest = { readonly optionIndex: number };

export type CastVoteRequest_skip_id_ = { readonly optionIndex: number };

export type CastVoteRequest_skip_value_ = { readonly optionIndex: number };

export type CreatePollRequest = {
  readonly options: string[];
  readonly question: string;
};

export type CreatePollRequest_skip_id_ = {
  readonly options: string[];
  readonly question: string;
};

export type CreatePollRequest_skip_value_ = {
  readonly options: string[];
  readonly question: string;
};

export type GetPollParams = { readonly pollId: string };

export type GetPollResultsParams = { readonly pollId: string };

export type GetVoteParams = {
  readonly pollId: string;
  readonly voterId: string;
};

export type ListPollsParams = { readonly ownerId?: string };

export type ListVotesForPollParams = { readonly pollId: string };

export type OptionTally = {
  readonly count: number;
  readonly optionIndex: number;
  readonly text: string;
  readonly votes: Vote[];
};

export type OptionTally_skip_id_ = {
  readonly count: number;
  readonly optionIndex: number;
  readonly text: string;
  readonly votes: Vote[];
};

export type OptionTally_skip_value_ = {
  readonly count: number;
  readonly optionIndex: number;
  readonly text: string;
  readonly votes: Vote[];
};

export type Poll = {
  readonly closed: boolean;
  readonly createdAt: string;
  readonly id: string;
  readonly options: PollOption[];
  readonly ownerId: string;
  readonly question: string;
};

export type PollList = {
  readonly limit: number;
  readonly offset: number;
  readonly polls: Poll[];
};

export type PollList_skip_id_ = {
  readonly limit: number;
  readonly offset: number;
  readonly polls: Poll[];
};

export type PollList_skip_value_ = {
  readonly limit: number;
  readonly offset: number;
  readonly polls: Poll[];
};

export type PollOption = {
  readonly optionIndex: number;
  readonly pollId: string;
  readonly text: string;
};

export type PollOption_skip_id_ = {
  readonly optionIndex: number;
  readonly pollId: string;
};

export type PollOption_skip_value_ = { readonly text: string };

export type PollResults = {
  readonly pollId: string;
  readonly tallies: OptionTally[];
  readonly totalVotes: number;
  readonly votes: Vote[];
};

export type PollResults_skip_id_ = {
  readonly pollId: string;
  readonly tallies: OptionTally[];
  readonly totalVotes: number;
  readonly votes: Vote[];
};

export type PollResults_skip_value_ = {
  readonly pollId: string;
  readonly tallies: OptionTally[];
  readonly totalVotes: number;
  readonly votes: Vote[];
};

export type PollStored = {
  readonly closed: boolean;
  readonly createdAt: string;
  readonly ownerId: string;
  readonly question: string;
};

export type Poll_skip_id_ = string;

export type Poll_skip_value_ = {
  readonly closed: boolean;
  readonly createdAt: string;
  readonly options: PollOption[];
  readonly ownerId: string;
  readonly question: string;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdatePollRequest = {
  readonly closed?: boolean;
  readonly question?: string;
};

export type UpdatePollRequest_skip_id_ = {
  readonly closed?: boolean;
  readonly question?: string;
};

export type UpdatePollRequest_skip_value_ = {
  readonly closed?: boolean;
  readonly question?: string;
};

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type Vote = {
  readonly castAt: string;
  readonly optionIndex: number;
  readonly pollId: string;
  readonly voterId: string;
};

export type VoteList = {
  readonly limit: number;
  readonly offset: number;
  readonly votes: Vote[];
};

export type VoteList_skip_id_ = {
  readonly limit: number;
  readonly offset: number;
  readonly votes: Vote[];
};

export type VoteList_skip_value_ = {
  readonly limit: number;
  readonly offset: number;
  readonly votes: Vote[];
};

export type Vote_skip_id_ = {
  readonly pollId: string;
  readonly voterId: string;
};

export type Vote_skip_value_ = {
  readonly castAt: string;
  readonly optionIndex: number;
};
