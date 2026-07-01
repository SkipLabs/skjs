import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPollResource } from "./resources/GetPollResource.js";
import { GetPollStoredResource } from "./resources/GetPollStoredResource.js";
import { GetVoteResource } from "./resources/GetVoteResource.js";
import { ListPollOptionsByPollResource } from "./resources/ListPollOptionsByPollResource.js";
import { ListPollsResource } from "./resources/ListPollsResource.js";
import { ListVotesByPollResource } from "./resources/ListVotesByPollResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  PollOptionKey,
  PollOptionStored,
  Poll_skip_id_,
  PollStored,
  User_skip_id_,
  User_skip_value_,
  VoteKey,
  VoteStored,
  ListPollsParams,
  Poll,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly pollOptions: InputDefinition<PollOptionKey, PollOptionStored>;
  readonly polls: InputDefinition<Poll_skip_id_, PollStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly votes: InputDefinition<VoteKey, VoteStored>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPollResource: ResourceClass<GraphCollections, Json>;
  readonly getPollStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getVoteResource: ResourceClass<GraphCollections, Json>;
  readonly listPollOptionsByPollResource: ResourceClass<GraphCollections, Json>;
  readonly listPollsResource: ResourceClass<GraphCollections, ListPollsParams>;
  readonly listVotesByPollResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      pollOptions: new InputDefinition<PollOptionKey, PollOptionStored>([]),
      polls: new InputDefinition<Poll_skip_id_, PollStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      votes: new InputDefinition<VoteKey, VoteStored>([]),
    };
    this.resources = {
      getPollResource: GetPollResource,
      getPollStoredResource: GetPollStoredResource,
      getVoteResource: GetVoteResource,
      listPollOptionsByPollResource: ListPollOptionsByPollResource,
      listPollsResource: ListPollsResource,
      listVotesByPollResource: ListVotesByPollResource,
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
