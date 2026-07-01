import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCommentByIdResource } from "./resources/GetCommentByIdResource.js";
import { GetLikeStoredResource } from "./resources/GetLikeStoredResource.js";
import { GetPostByIdResource } from "./resources/GetPostByIdResource.js";
import { GetPostStoredResource } from "./resources/GetPostStoredResource.js";
import { ListFeedResource } from "./resources/ListFeedResource.js";
import { ListPostCommentsResource } from "./resources/ListPostCommentsResource.js";
import { ListPostLikesResource } from "./resources/ListPostLikesResource.js";
import { ListPostsResource } from "./resources/ListPostsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  LikeKey,
  LikeStored,
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
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly comments: InputDefinition<Comment_skip_id_, Comment_skip_value_>;
  readonly likes: InputDefinition<LikeKey, LikeStored>;
  readonly posts: InputDefinition<Post_skip_id_, PostStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCommentByIdResource: ResourceClass<GraphCollections, Json>;
  readonly getLikeStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getPostByIdResource: ResourceClass<GraphCollections, Json>;
  readonly getPostStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listFeedResource: ResourceClass<GraphCollections, Json>;
  readonly listPostCommentsResource: ResourceClass<GraphCollections, Json>;
  readonly listPostLikesResource: ResourceClass<GraphCollections, Json>;
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

  constructor() {
    this.inputs = {
      comments: new InputDefinition<Comment_skip_id_, Comment_skip_value_>([]),
      likes: new InputDefinition<LikeKey, LikeStored>([]),
      posts: new InputDefinition<Post_skip_id_, PostStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCommentByIdResource: GetCommentByIdResource,
      getLikeStoredResource: GetLikeStoredResource,
      getPostByIdResource: GetPostByIdResource,
      getPostStoredResource: GetPostStoredResource,
      listFeedResource: ListFeedResource,
      listPostCommentsResource: ListPostCommentsResource,
      listPostLikesResource: ListPostLikesResource,
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
