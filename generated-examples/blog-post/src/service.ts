import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCommentStoredResource } from "./resources/GetCommentStoredResource.js";
import { GetPostByIdResource } from "./resources/GetPostByIdResource.js";
import { GetPostStoredResource } from "./resources/GetPostStoredResource.js";
import { ListCommentsForPostResource } from "./resources/ListCommentsForPostResource.js";
import { ListPostsResource } from "./resources/ListPostsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  PostStored,
  User_skip_id_,
  User_skip_value_,
  ListPostsParams,
  Comment,
  Post,
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
  readonly comments: InputDefinition<Comment_skip_id_, Comment_skip_value_>;
  readonly posts: InputDefinition<Post_skip_id_, PostStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCommentStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getPostByIdResource: ResourceClass<GraphCollections, Json>;
  readonly getPostStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listCommentsForPostResource: ResourceClass<GraphCollections, Json>;
  readonly listPostsResource: ResourceClass<GraphCollections, ListPostsParams>;
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
      comments: new InputDefinition<Comment_skip_id_, Comment_skip_value_>([]),
      posts: new InputDefinition<Post_skip_id_, PostStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCommentStoredResource: GetCommentStoredResource,
      getPostByIdResource: GetPostByIdResource,
      getPostStoredResource: GetPostStoredResource,
      listCommentsForPostResource: ListCommentsForPostResource,
      listPostsResource: ListPostsResource,
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
