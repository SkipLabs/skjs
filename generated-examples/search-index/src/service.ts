import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPostStoredResource } from "./resources/GetPostStoredResource.js";
import { GetSearchDocumentByPostIdResource } from "./resources/GetSearchDocumentByPostIdResource.js";
import { GetTagStoredResource } from "./resources/GetTagStoredResource.js";
import { ListPostsResource } from "./resources/ListPostsResource.js";
import { ListTagsResource } from "./resources/ListTagsResource.js";
import { SearchResource } from "./resources/SearchResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Post_skip_id_,
  PostStored,
  Tag_skip_id_,
  Tag_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListPostsParams,
  ListTagsParams,
  SearchParams,
  Post,
  Tag,
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
  readonly posts: InputDefinition<Post_skip_id_, PostStored>;
  readonly tags: InputDefinition<Tag_skip_id_, Tag_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPostStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getSearchDocumentByPostIdResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly getTagStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listPostsResource: ResourceClass<GraphCollections, ListPostsParams>;
  readonly listTagsResource: ResourceClass<GraphCollections, ListTagsParams>;
  readonly searchResource: ResourceClass<GraphCollections, SearchParams>;
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
      posts: new InputDefinition<Post_skip_id_, PostStored>([]),
      tags: new InputDefinition<Tag_skip_id_, Tag_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getPostStoredResource: GetPostStoredResource,
      getSearchDocumentByPostIdResource: GetSearchDocumentByPostIdResource,
      getTagStoredResource: GetTagStoredResource,
      listPostsResource: ListPostsResource,
      listTagsResource: ListTagsResource,
      searchResource: SearchResource,
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
