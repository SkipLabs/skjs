import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCommentResource } from "./resources/GetCommentResource.js";
import { GetCommentStoredResource } from "./resources/GetCommentStoredResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { ListAllCommentLikesResource } from "./resources/ListAllCommentLikesResource.js";
import { ListCommentLikesResource } from "./resources/ListCommentLikesResource.js";
import { ListCommentsResource } from "./resources/ListCommentsResource.js";
import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  Comment_skip_id_,
  CommentStored,
  User_skip_id_,
  User_skip_value_,
  CommentLike,
  Comment,
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
  readonly commentLikes: InputDefinition<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
  readonly comments: InputDefinition<Comment_skip_id_, CommentStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCommentResource: ResourceClass<GraphCollections, Json>;
  readonly getCommentStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, Json>;
  readonly listAllCommentLikesResource: ResourceClass<GraphCollections, Json>;
  readonly listCommentLikesResource: ResourceClass<GraphCollections, Json>;
  readonly listCommentsResource: ResourceClass<GraphCollections, Json>;
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
      commentLikes: new InputDefinition<
        CommentLike_skip_id_,
        CommentLike_skip_value_
      >([]),
      comments: new InputDefinition<Comment_skip_id_, CommentStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCommentResource: GetCommentResource,
      getCommentStoredResource: GetCommentStoredResource,
      getUserResource: GetUserResource,
      listAllCommentLikesResource: ListAllCommentLikesResource,
      listCommentLikesResource: ListCommentLikesResource,
      listCommentsResource: ListCommentsResource,
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
