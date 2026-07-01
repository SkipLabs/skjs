import type {
  PollOption_skip_id_,
  PollOption,
  PollOption_skip_value_,
  Poll_skip_id_,
  Poll,
  PollStored,
  User_skip_id_,
  User,
  User_skip_value_,
  Vote_skip_id_,
  Vote,
  Vote_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly pollOptions: EagerCollection<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: EagerCollection<Poll_skip_id_, PollStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly votes: EagerCollection<Vote_skip_id_, Vote_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_pollOptions = inputs.pollOptions;
  const output_polls = inputs.polls;
  const output_users = inputs.users;
  const output_votes = inputs.votes;
  return {
    pollOptions: output_pollOptions,
    polls: output_polls,
    users: output_users,
    votes: output_votes,
  };
}
