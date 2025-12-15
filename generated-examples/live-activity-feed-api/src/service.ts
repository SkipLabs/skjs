import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

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


type Inputs = {
  posts: Entry<PostId, PostValue>[];
  comments: Entry<CommentId, CommentValue>[];
  likes: Entry<LikeId, LikeValue>[];
  users: Entry<UserId, UserValue>[];
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

type Resources = {
  "feed": new (params: Json) => Resource<GraphCollections>;
  "posts": new (params: Json) => Resource<GraphCollections>;
};

export class PostToFeedItemMapper implements Mapper<PostId, PostValue, FeedItemId, FeedItemValue> {
  constructor() {
  }

  mapEntry(
    key: PostId,
    values: Values<PostValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const arr = values.toArray();
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<FeedItemId, FeedItemValue> {
    return cs.feed;
  }
}

export class PostsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PostId, PostValue> {
    return cs.posts;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyPosts: Entry<PostId, PostValue>[] = Array.of();
    const emptyComments: Entry<CommentId, CommentValue>[] = Array.of();
    const emptyLikes: Entry<LikeId, LikeValue>[] = Array.of();
    const emptyUsers: Entry<UserId, UserValue>[] = Array.of();
    this.initialData = { posts: emptyPosts, comments: emptyComments, likes: emptyLikes, users: emptyUsers };
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
