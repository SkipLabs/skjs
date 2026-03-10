import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  PostId,
  PostValue,
  CommentId,
  CommentValue,
  LikeId,
  LikeValue,
  UserId,
  UserValue,
  FeedItemId,
  FeedItemValue,
} from "./types.js";


export type Inputs = {
  posts: InputDefinition<PostId, PostValue>;
  comments: InputDefinition<CommentId, CommentValue>;
  likes: InputDefinition<LikeId, LikeValue>;
  users: InputDefinition<UserId, UserValue>;
};

export type InputCollections = {
  posts: EagerCollection<PostId, PostValue>;
  comments: EagerCollection<CommentId, CommentValue>;
  likes: EagerCollection<LikeId, LikeValue>;
  users: EagerCollection<UserId, UserValue>;
};

export type GraphCollections = {
  posts: EagerCollection<PostId, PostValue>;
  feed: EagerCollection<FeedItemId, FeedItemValue>;
};

export type Resources = {
  readonly "feed": ResourceClass<GraphCollections, {}>;
  readonly "posts": ResourceClass<GraphCollections, {}>;
};

export class PostToFeedItemMapper implements Mapper<PostId, PostValue, FeedItemId, FeedItemValue> {
  constructor() {
  }

  mapEntry(
    key: PostId,
    values: Values<PostValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (const v of values) {
      const feedItemId: FeedItemId = key;
      const feedItemValue: FeedItemValue = {
        type: "post",
        actorId: v.authorId,
        targetId: key,
        content: v.content,
        timestamp: v.createdAt
      };
      result.push([feedItemId, feedItemValue]);
    }
    return result;
  }
}

export class CommentToFeedItemMapper implements Mapper<CommentId, CommentValue, FeedItemId, FeedItemValue> {
  constructor() {
  }

  mapEntry(
    key: CommentId,
    values: Values<CommentValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (const v of values) {
      const feedItemId: FeedItemId = key;
      const feedItemValue: FeedItemValue = {
        type: "comment",
        actorId: v.authorId,
        targetId: v.postId,
        content: v.content,
        timestamp: v.createdAt
      };
      result.push([feedItemId, feedItemValue]);
    }
    return result;
  }
}

export class LikeToFeedItemMapper implements Mapper<LikeId, LikeValue, FeedItemId, FeedItemValue> {
  constructor() {
  }

  mapEntry(
    key: LikeId,
    values: Values<LikeValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (const v of values) {
      const feedItemId: FeedItemId = key;
      const feedItemValue: FeedItemValue = {
        type: "like",
        actorId: v.userId,
        targetId: v.postId,
        content: null,
        timestamp: v.createdAt
      };
      result.push([feedItemId, feedItemValue]);
    }
    return result;
  }
}


export class FeedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<FeedItemId, FeedItemValue> {
    return cs.feed;
  }
}

export class PostsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PostId, PostValue> {
    return cs.posts;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                    this.inputs = { posts: new InputDefinition<PostId, PostValue>([]), comments: new InputDefinition<CommentId, CommentValue>([]), likes: new InputDefinition<LikeId, LikeValue>([]), users: new InputDefinition<UserId, UserValue>([]) };
    this.resources = { "feed": FeedResource, "posts": PostsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const postFeedItems = inputs.posts.map(PostToFeedItemMapper);
    const commentFeedItems = inputs.comments.map(CommentToFeedItemMapper);
    const likeFeedItems = inputs.likes.map(LikeToFeedItemMapper);
    
    const feed = postFeedItems.merge(commentFeedItems, likeFeedItems);
    
    return { posts: inputs.posts, feed: feed };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
