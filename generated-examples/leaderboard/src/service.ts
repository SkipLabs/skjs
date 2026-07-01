import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetLeaderboardResource } from "./resources/GetLeaderboardResource.js";
import { GetMyLeaderboardEntryResource } from "./resources/GetMyLeaderboardEntryResource.js";
import { GetScoreByIdResource } from "./resources/GetScoreByIdResource.js";
import { ListScoresResource } from "./resources/ListScoresResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetMyLeaderboardEntryParams,
  ListScoresParams,
  ScoreEntry,
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
  readonly scores: InputDefinition<ScoreEntry_skip_id_, ScoreEntry_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getLeaderboardResource: ResourceClass<GraphCollections, Json>;
  readonly getMyLeaderboardEntryResource: ResourceClass<
    GraphCollections,
    GetMyLeaderboardEntryParams
  >;
  readonly getScoreByIdResource: ResourceClass<GraphCollections, Json>;
  readonly listScoresResource: ResourceClass<
    GraphCollections,
    ListScoresParams
  >;
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
      scores: new InputDefinition<ScoreEntry_skip_id_, ScoreEntry_skip_value_>(
        [],
      ),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getLeaderboardResource: GetLeaderboardResource,
      getMyLeaderboardEntryResource: GetMyLeaderboardEntryResource,
      getScoreByIdResource: GetScoreByIdResource,
      listScoresResource: ListScoresResource,
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
