import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPollResource } from "./resources/GetPollResource.js";
import { GetPollResultsResource } from "./resources/GetPollResultsResource.js";
import { GetPollStoredResource } from "./resources/GetPollStoredResource.js";
import { GetVoteResource } from "./resources/GetVoteResource.js";
import { ListPollOptionsByPollResource } from "./resources/ListPollOptionsByPollResource.js";
import { ListPollsResource } from "./resources/ListPollsResource.js";
import { ListVotesForPollResource } from "./resources/ListVotesForPollResource.js";
import { VotesByPollResource } from "./resources/VotesByPollResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  PollOption_skip_id_,
  PollOption_skip_value_,
  Poll_skip_id_,
  PollStored,
  User_skip_id_,
  User_skip_value_,
  Vote_skip_id_,
  Vote_skip_value_,
  GetPollResultsParams,
  ListPollsParams,
  ListVotesForPollParams,
  PollOption,
  Poll,
  User,
  Vote,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly pollOptions: InputDefinition<
    PollOption_skip_id_,
    PollOption_skip_value_
  >;
  readonly polls: InputDefinition<Poll_skip_id_, PollStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly votes: InputDefinition<Vote_skip_id_, Vote_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPollResource: ResourceClass<GraphCollections, Json>;
  readonly getPollResultsResource: ResourceClass<
    GraphCollections,
    GetPollResultsParams
  >;
  readonly getPollStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getVoteResource: ResourceClass<GraphCollections, Json>;
  readonly listPollOptionsByPollResource: ResourceClass<GraphCollections, Json>;
  readonly listPollsResource: ResourceClass<GraphCollections, ListPollsParams>;
  readonly listVotesForPollResource: ResourceClass<
    GraphCollections,
    ListVotesForPollParams
  >;
  readonly votesByPollResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      pollOptions: new InputDefinition<
        PollOption_skip_id_,
        PollOption_skip_value_
      >([]),
      polls: new InputDefinition<Poll_skip_id_, PollStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      votes: new InputDefinition<Vote_skip_id_, Vote_skip_value_>([]),
    };
    this.resources = {
      getPollResource: GetPollResource,
      getPollResultsResource: GetPollResultsResource,
      getPollStoredResource: GetPollStoredResource,
      getVoteResource: GetVoteResource,
      listPollOptionsByPollResource: ListPollOptionsByPollResource,
      listPollsResource: ListPollsResource,
      listVotesForPollResource: ListVotesForPollResource,
      votesByPollResource: VotesByPollResource,
      getMeResource: getMeResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
