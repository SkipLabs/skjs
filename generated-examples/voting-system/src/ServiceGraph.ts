import { AssemblePollMapper } from "./mappers/AssemblePollMapper.js";
import { PollOptionByPollMapper } from "./mappers/PollOptionByPollMapper.js";
import { VoteByPollMapper } from "./mappers/VoteByPollMapper.js";
import { VoteCountByOptionMapper } from "./mappers/VoteCountByOptionMapper.js";
import { VoteCountByPollMapper } from "./mappers/VoteCountByPollMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  PollOptionKey,
  PollOptionStored,
  Poll_skip_id_,
  Poll,
  PollStored,
  User_skip_id_,
  User,
  User_skip_value_,
  VoteKey,
  VoteStored,
  PollOption,
  Poll_skip_value_,
  Vote,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly pollOptions: EagerCollection<PollOptionKey, PollOptionStored>;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly votes: EagerCollection<VoteKey, VoteStored>;
}

export interface GraphCollections extends SharedCollections {
  readonly optionsByPoll: EagerCollection<Poll_skip_id_, PollOption>;
  readonly polls: EagerCollection<Poll_skip_id_, Poll_skip_value_>;
  readonly pollsStored: EagerCollection<Poll_skip_id_, PollStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly votes: EagerCollection<VoteKey, VoteStored>;
  readonly votesByPoll: EagerCollection<Poll_skip_id_, Vote>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const voteCountByOption = inputs.votes.map(VoteCountByOptionMapper);
  const voteCountByOptionAgg = voteCountByOption.reduce(SumReducer);
  const optionsByPoll = inputs.pollOptions.map(
    PollOptionByPollMapper,
    voteCountByOptionAgg,
  );
  const voteCountByPoll = inputs.votes.map(VoteCountByPollMapper);
  const voteCountByPollAgg = voteCountByPoll.reduce(SumReducer);
  const assembledPolls = inputs.polls.map(
    AssemblePollMapper,
    optionsByPoll,
    voteCountByPollAgg,
  );
  const output_optionsByPoll = optionsByPoll;
  const output_polls = assembledPolls;
  const output_pollsStored = inputs.polls;
  const output_users = inputs.users;
  const output_votes = inputs.votes;
  const votesByPoll = inputs.votes.map(VoteByPollMapper);
  const output_votesByPoll = votesByPoll;
  return {
    optionsByPoll: output_optionsByPoll,
    polls: output_polls,
    pollsStored: output_pollsStored,
    users: output_users,
    votes: output_votes,
    votesByPoll: output_votesByPoll,
  };
}
