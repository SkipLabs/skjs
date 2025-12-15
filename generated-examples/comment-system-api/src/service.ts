import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "@skipruntime/core";

import type {
  CommentId,
  CommentValue,
  ReplyId,
  ReplyValue,
  LikeId,
  LikeValue,
  CommentWithStatsId,
  CommentWithStatsValue,
  FeedItemId,
  FeedItemValue,
  RepliesByCommentResourceParams,
  LikesByCommentResourceParams,
} from "./types.js";

export type CountAccum = {
  count: number;
};

type Inputs = {
  comments: Entry<CommentId, CommentValue>[];
  replies: Entry<ReplyId, ReplyValue>[];
  likes: Entry<LikeId, LikeValue>[];
};

export type InputCollections = {
  comments: EagerCollection<CommentId, CommentValue>;
  replies: EagerCollection<ReplyId, ReplyValue>;
  likes: EagerCollection<LikeId, LikeValue>;
};

export type GraphCollections = {
  comments: EagerCollection<CommentId, CommentValue>;
  replies: EagerCollection<ReplyId, ReplyValue>;
  likes: EagerCollection<LikeId, LikeValue>;
  replyCountsByComment: EagerCollection<CommentId, CountAccum>;
  likeCountsByComment: EagerCollection<CommentId, CountAccum>;
  commentsWithStats: EagerCollection<CommentWithStatsId, CommentWithStatsValue>;
  repliesByComment: EagerCollection<CommentId, ReplyValue>;
  likesByComment: EagerCollection<CommentId, LikeValue>;
  feed: EagerCollection<FeedItemId, FeedItemValue>;
};

type Resources = {
  "comments": new (params: Json) => Resource<GraphCollections>;
  "repliesByComment": new (params: Json) => Resource<GraphCollections>;
  "likesByComment": new (params: Json) => Resource<GraphCollections>;
  "feed": new (params: Json) => Resource<GraphCollections>;
};

export class ReplyToCommentKeyMapper implements Mapper<ReplyId, ReplyValue, CommentId, number> {
  constructor() {}

  mapEntry(
    _key: ReplyId,
    values: Values<ReplyValue>,
    _context: Context
  ): Iterable<[CommentId, number]> {
    const arr = values.toArray();
    const result: Array<[CommentId, number]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([v.commentId, 1]);
    }
    return result;
  }
}

export class LikeToCommentKeyMapper implements Mapper<LikeId, LikeValue, CommentId, number> {
  constructor() {}

  mapEntry(
    _key: LikeId,
    values: Values<LikeValue>,
    _context: Context
  ): Iterable<[CommentId, number]> {
    const arr = values.toArray();
    const result: Array<[CommentId, number]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([v.commentId, 1]);
    }
    return result;
  }
}

export class CommentWithStatsMapper implements Mapper<CommentId, CommentValue, CommentWithStatsId, CommentWithStatsValue> {
  private replyCountsByComment: EagerCollection<CommentId, CountAccum>;
  private likeCountsByComment: EagerCollection<CommentId, CountAccum>;

  constructor(
    replyCountsByComment: EagerCollection<CommentId, CountAccum>,
    likeCountsByComment: EagerCollection<CommentId, CountAccum>
  ) {
    this.replyCountsByComment = replyCountsByComment;
    this.likeCountsByComment = likeCountsByComment;
  }

  mapEntry(
    key: CommentId,
    values: Values<CommentValue>,
    _context: Context
  ): Iterable<[CommentWithStatsId, CommentWithStatsValue]> {
    const arr = values.toArray();
    const result: Array<[CommentWithStatsId, CommentWithStatsValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const replyCountArr = this.replyCountsByComment.getArray(key);
      const likeCountArr = this.likeCountsByComment.getArray(key);
      const replyCount = replyCountArr.length > 0 ? replyCountArr[0]!.count : 0;
      const likeCount = likeCountArr.length > 0 ? likeCountArr[0]!.count : 0;
      result.push([key, {
        authorId: v.authorId,
        content: v.content,
        createdAt: v.createdAt,
        replyCount: replyCount,
        likeCount: likeCount
      }]);
    }
    return result;
  }
}

export class ReplyByCommentMapper implements Mapper<ReplyId, ReplyValue, CommentId, ReplyValue> {
  constructor() {}

  mapEntry(
    _key: ReplyId,
    values: Values<ReplyValue>,
    _context: Context
  ): Iterable<[CommentId, ReplyValue]> {
    const arr = values.toArray();
    const result: Array<[CommentId, ReplyValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([v.commentId, v]);
    }
    return result;
  }
}

export class LikeByCommentMapper implements Mapper<LikeId, LikeValue, CommentId, LikeValue> {
  constructor() {}

  mapEntry(
    _key: LikeId,
    values: Values<LikeValue>,
    _context: Context
  ): Iterable<[CommentId, LikeValue]> {
    const arr = values.toArray();
    const result: Array<[CommentId, LikeValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([v.commentId, v]);
    }
    return result;
  }
}

export class CommentToFeedItemMapper implements Mapper<CommentId, CommentValue, FeedItemId, FeedItemValue> {
  constructor() {}

  mapEntry(
    key: CommentId,
    values: Values<CommentValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const arr = values.toArray();
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([key, {
        type: "comment",
        authorId: v.authorId,
        content: v.content,
        createdAt: v.createdAt,
        parentId: null
      }]);
    }
    return result;
  }
}

export class ReplyToFeedItemMapper implements Mapper<ReplyId, ReplyValue, FeedItemId, FeedItemValue> {
  constructor() {}

  mapEntry(
    key: ReplyId,
    values: Values<ReplyValue>,
    _context: Context
  ): Iterable<[FeedItemId, FeedItemValue]> {
    const arr = values.toArray();
    const result: Array<[FeedItemId, FeedItemValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      result.push([key, {
        type: "reply",
        authorId: v.authorId,
        content: v.content,
        createdAt: v.createdAt,
        parentId: v.commentId
      }]);
    }
    return result;
  }
}

export class FilterByCommentIdMapper implements Mapper<CommentId, ReplyValue, ReplyId, ReplyValue> {
  private commentId: CommentId;

  constructor(commentId: CommentId) {
    this.commentId = commentId;
  }

  mapEntry(
    key: CommentId,
    values: Values<ReplyValue>,
    _context: Context
  ): Iterable<[ReplyId, ReplyValue]> {
    const result: Array<[ReplyId, ReplyValue]> = Array.of();
    if (key !== this.commentId) {
      return result;
    }
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const replyId = JSON.stringify([v.commentId, v.authorId, v.createdAt]);
      result.push([replyId, v]);
    }
    return result;
  }
}

export class FilterLikesByCommentIdMapper implements Mapper<CommentId, LikeValue, LikeId, LikeValue> {
  private commentId: CommentId;

  constructor(commentId: CommentId) {
    this.commentId = commentId;
  }

  mapEntry(
    key: CommentId,
    values: Values<LikeValue>,
    _context: Context
  ): Iterable<[LikeId, LikeValue]> {
    const result: Array<[LikeId, LikeValue]> = Array.of();
    if (key !== this.commentId) {
      return result;
    }
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      const likeId = JSON.stringify([v.commentId, v.userId, v.createdAt]);
      result.push([likeId, v]);
    }
    return result;
  }
}

export class CountReducer implements Reducer<number, CountAccum> {
  initial: Nullable<CountAccum> = null;

  constructor() {}

  add(accum: Nullable<CountAccum>, value: number & DepSafe): CountAccum {
    if (accum === null) {
      return { count: value };
    }
    return { count: accum.count + value };
  }

  remove(accum: CountAccum, value: number & DepSafe): Nullable<CountAccum> {
    const newCount = accum.count - value;
    if (newCount <= 0) {
      return null;
    }
    return { count: newCount };
  }
}

export class CommentsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {}

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CommentId, CommentValue> {
    return cs.comments;
  }
}

export class RepliesByCommentResource implements Resource<GraphCollections> {
  private commentId: string;

  constructor(params: Json) {
    const typed = params as RepliesByCommentResourceParams;
    this.commentId = typed.commentId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReplyId, ReplyValue> {
    return cs.repliesByComment.map(FilterByCommentIdMapper, this.commentId);
  }
}

export class LikesByCommentResource implements Resource<GraphCollections> {
  private commentId: string;

  constructor(params: Json) {
    const typed = params as LikesByCommentResourceParams;
    this.commentId = typed.commentId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LikeId, LikeValue> {
    return cs.likesByComment.map(FilterLikesByCommentIdMapper, this.commentId);
  }
}

export class FeedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {}

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
    const emptyComments: Entry<CommentId, CommentValue>[] = Array.of();
    const emptyReplies: Entry<ReplyId, ReplyValue>[] = Array.of();
    const emptyLikes: Entry<LikeId, LikeValue>[] = Array.of();
    this.initialData = { comments: emptyComments, replies: emptyReplies, likes: emptyLikes };
    this.resources = { "comments": CommentsResource, "repliesByComment": RepliesByCommentResource, "likesByComment": LikesByCommentResource, "feed": FeedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const replyCountsByComment = inputs.replies.map(ReplyToCommentKeyMapper).reduce(CountReducer);
    const likeCountsByComment = inputs.likes.map(LikeToCommentKeyMapper).reduce(CountReducer);
    const commentsWithStats = inputs.comments.map(CommentWithStatsMapper, replyCountsByComment, likeCountsByComment);
    const repliesByComment = inputs.replies.map(ReplyByCommentMapper);
    const likesByComment = inputs.likes.map(LikeByCommentMapper);
    const commentFeedItems = inputs.comments.map(CommentToFeedItemMapper);
    const replyFeedItems = inputs.replies.map(ReplyToFeedItemMapper);
    const feed = commentFeedItems.merge(replyFeedItems);
    return {
      comments: inputs.comments,
      replies: inputs.replies,
      likes: inputs.likes,
      replyCountsByComment: replyCountsByComment,
      likeCountsByComment: likeCountsByComment,
      commentsWithStats: commentsWithStats,
      repliesByComment: repliesByComment,
      likesByComment: likesByComment,
      feed: feed
    };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
