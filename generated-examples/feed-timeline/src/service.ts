import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCommentByIdResource } from "./resources/GetCommentByIdResource.js";
import { GetFeedResource } from "./resources/GetFeedResource.js";
import { GetPostByIdResource } from "./resources/GetPostByIdResource.js";
import { GetPostStoredResource } from "./resources/GetPostStoredResource.js";
import { GetUserByIdResource } from "./resources/GetUserByIdResource.js";
import { ListCommentsByPostResource } from "./resources/ListCommentsByPostResource.js";
import { ListLikesByPostResource } from "./resources/ListLikesByPostResource.js";
import { ListLikesRawResource } from "./resources/ListLikesRawResource.js";
import { ListPostsResource } from "./resources/ListPostsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Like_skip_id_,
  Like_skip_value_,
  Post_skip_id_,
  PostStored,
  User_skip_id_,
  User_skip_value_,
  GetPostByIdParams,
  GetUserByIdParams,
  ListCommentsByPostParams,
  ListLikesByPostParams,
  Comment,
  Like,
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
  readonly likes: InputDefinition<Like_skip_id_, Like_skip_value_>;
  readonly posts: InputDefinition<Post_skip_id_, PostStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCommentByIdResource: ResourceClass<GraphCollections, Json>;
  readonly getFeedResource: ResourceClass<GraphCollections, Json>;
  readonly getPostByIdResource: ResourceClass<
    GraphCollections,
    GetPostByIdParams
  >;
  readonly getPostStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUserByIdResource: ResourceClass<
    GraphCollections,
    GetUserByIdParams
  >;
  readonly listCommentsByPostResource: ResourceClass<
    GraphCollections,
    ListCommentsByPostParams
  >;
  readonly listLikesByPostResource: ResourceClass<
    GraphCollections,
    ListLikesByPostParams
  >;
  readonly listLikesRawResource: ResourceClass<GraphCollections, Json>;
  readonly listPostsResource: ResourceClass<GraphCollections, Json>;
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
      likes: new InputDefinition<Like_skip_id_, Like_skip_value_>([]),
      posts: new InputDefinition<Post_skip_id_, PostStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCommentByIdResource: GetCommentByIdResource,
      getFeedResource: GetFeedResource,
      getPostByIdResource: GetPostByIdResource,
      getPostStoredResource: GetPostStoredResource,
      getUserByIdResource: GetUserByIdResource,
      listCommentsByPostResource: ListCommentsByPostResource,
      listLikesByPostResource: ListLikesByPostResource,
      listLikesRawResource: ListLikesRawResource,
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
