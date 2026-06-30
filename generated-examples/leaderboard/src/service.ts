import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetBoardRankingsResource } from "./resources/GetBoardRankingsResource.js";
import { GetBoardResource } from "./resources/GetBoardResource.js";
import { GetScoreEntryResource } from "./resources/GetScoreEntryResource.js";
import { ListBoardEntriesResource } from "./resources/ListBoardEntriesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Board_skip_id_,
  Board_skip_value_,
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetBoardRankingsParams,
  ListBoardEntriesParams,
  Board,
  ScoreEntry,
  User,
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
  readonly boards: InputDefinition<Board_skip_id_, Board_skip_value_>;
  readonly scoreEntries: InputDefinition<
    ScoreEntry_skip_id_,
    ScoreEntry_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getBoardRankingsResource: ResourceClass<
    GraphCollections,
    GetBoardRankingsParams
  >;
  readonly getBoardResource: ResourceClass<GraphCollections, Json>;
  readonly getScoreEntryResource: ResourceClass<GraphCollections, Json>;
  readonly listBoardEntriesResource: ResourceClass<
    GraphCollections,
    ListBoardEntriesParams
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

  constructor() {
    this.inputs = {
      boards: new InputDefinition<Board_skip_id_, Board_skip_value_>([]),
      scoreEntries: new InputDefinition<
        ScoreEntry_skip_id_,
        ScoreEntry_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getBoardRankingsResource: GetBoardRankingsResource,
      getBoardResource: GetBoardResource,
      getScoreEntryResource: GetScoreEntryResource,
      listBoardEntriesResource: ListBoardEntriesResource,
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
