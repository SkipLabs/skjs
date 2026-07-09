import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPostStoredResource } from "./resources/GetPostStoredResource.js";
import { ListPostTagsByPostResource } from "./resources/ListPostTagsByPostResource.js";
import { ListPostsResource } from "./resources/ListPostsResource.js";
import { ListTagsResource } from "./resources/ListTagsResource.js";
import { PostTagsByTagResource } from "./resources/PostTagsByTagResource.js";
import { SearchDocumentsResource } from "./resources/SearchDocumentsResource.js";
import { TagByNameResource } from "./resources/TagByNameResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  PostTagKey,
  PostTagStored,
  Post_skip_id_,
  PostStored,
  Tag_skip_id_,
  Tag_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Post,
  Tag,
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
  readonly postTags: InputDefinition<PostTagKey, PostTagStored>;
  readonly posts: InputDefinition<Post_skip_id_, PostStored>;
  readonly tags: InputDefinition<Tag_skip_id_, Tag_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPostStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listPostTagsByPostResource: ResourceClass<GraphCollections, Json>;
  readonly listPostsResource: ResourceClass<GraphCollections, Json>;
  readonly listTagsResource: ResourceClass<GraphCollections, Json>;
  readonly postTagsByTagResource: ResourceClass<GraphCollections, Json>;
  readonly searchDocumentsResource: ResourceClass<GraphCollections, Json>;
  readonly tagByNameResource: ResourceClass<GraphCollections, Json>;
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
      postTags: new InputDefinition<PostTagKey, PostTagStored>([]),
      posts: new InputDefinition<Post_skip_id_, PostStored>([]),
      tags: new InputDefinition<Tag_skip_id_, Tag_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getPostStoredResource: GetPostStoredResource,
      listPostTagsByPostResource: ListPostTagsByPostResource,
      listPostsResource: ListPostsResource,
      listTagsResource: ListTagsResource,
      postTagsByTagResource: PostTagsByTagResource,
      searchDocumentsResource: SearchDocumentsResource,
      tagByNameResource: TagByNameResource,
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
