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
  LikeId,
  LikeValue,
  CommentId,
  CommentValue,
  FeedItemId,
  FeedItemValue,
} from "./types.js";


type Inputs = {
  posts: Entry<PostId, PostValue>[];
  likes: Entry<LikeId, LikeValue>[];
  comments: Entry<CommentId, CommentValue>[];
};

export type InputCollections = {
  posts: EagerCollection<PostId, PostValue>;
  likes: EagerCollection<LikeId, LikeValue>;
  comments: EagerCollection<CommentId, CommentValue>;
};

export type GraphCollections = {
  feed: EagerCollection<FeedItemId, FeedItemValue>;
};

type Resources = {
  "feed": new (params: Json) => Resource<GraphCollections>;
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
        itemType: "post",
        authorId: v.authorId,
        content: v.content,
        targetId: null,
        targetType: null,
        postId: null,
        timestamp: v.timestamp
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
        itemType: "like",
        authorId: v.userId,
        content: null,
        targetId: v.targetId,
        targetType: v.targetType,
        postId: null,
        timestamp: v.timestamp
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
        itemType: "comment",
        authorId: v.authorId,
        content: v.content,
        targetId: null,
        targetType: null,
        postId: v.postId,
        timestamp: v.timestamp
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

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyPosts: Entry<PostId, PostValue>[] = Array.of();
    const emptyLikes: Entry<LikeId, LikeValue>[] = Array.of();
    const emptyComments: Entry<CommentId, CommentValue>[] = Array.of();
    this.initialData = { posts: emptyPosts, likes: emptyLikes, comments: emptyComments };
    this.resources = { "feed": FeedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const postFeedItems = inputs.posts.map(PostToFeedItemMapper);
    const likeFeedItems = inputs.likes.map(LikeToFeedItemMapper);
    const commentFeedItems = inputs.comments.map(CommentToFeedItemMapper);
    
    const feed = postFeedItems.merge(likeFeedItems, commentFeedItems);
    
    return { feed };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
