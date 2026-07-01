import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCommentLikeStoredResource } from "./resources/GetCommentLikeStoredResource.js";
import { GetCommentResource } from "./resources/GetCommentResource.js";
import { GetCommentStoredResource } from "./resources/GetCommentStoredResource.js";
import { ListCommentLikesResource } from "./resources/ListCommentLikesResource.js";
import { ListCommentsResource } from "./resources/ListCommentsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  CommentStored,
  User_skip_id_,
  User_skip_value_,
  ListCommentLikesParams,
  ListCommentsParams,
  CommentLike,
  Comment,
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
  readonly commentLikes: InputDefinition<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
  readonly comments: InputDefinition<Comment_skip_id_, CommentStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCommentLikeStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getCommentResource: ResourceClass<GraphCollections, Json>;
  readonly getCommentStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listCommentLikesResource: ResourceClass<
    GraphCollections,
    ListCommentLikesParams
  >;
  readonly listCommentsResource: ResourceClass<
    GraphCollections,
    ListCommentsParams
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
      commentLikes: new InputDefinition<
        CommentLike_skip_id_,
        CommentLike_skip_value_
      >([]),
      comments: new InputDefinition<Comment_skip_id_, CommentStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCommentLikeStoredResource: GetCommentLikeStoredResource,
      getCommentResource: GetCommentResource,
      getCommentStoredResource: GetCommentStoredResource,
      listCommentLikesResource: ListCommentLikesResource,
      listCommentsResource: ListCommentsResource,
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
