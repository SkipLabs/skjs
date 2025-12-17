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
  AuthorId,
  AuthorValue,
  PostId,
  PostValue,
  CommentId,
  CommentValue,
  AuthorsPostsResourceParams,
  PostsCommentsResourceParams,
} from "./types.js";


type Inputs = {
  authors: Entry<AuthorId, AuthorValue>[];
  posts: Entry<PostId, PostValue>[];
  comments: Entry<CommentId, CommentValue>[];
};

export type InputCollections = {
  authors: EagerCollection<AuthorId, AuthorValue>;
  posts: EagerCollection<PostId, PostValue>;
  comments: EagerCollection<CommentId, CommentValue>;
};

export type GraphCollections = {
  authors: EagerCollection<AuthorId, AuthorValue>;
  posts: EagerCollection<PostId, PostValue>;
  comments: EagerCollection<CommentId, CommentValue>;
};

type Resources = {
  "authors": new (params: Json) => Resource<GraphCollections>;
  "posts": new (params: Json) => Resource<GraphCollections>;
  "posts-published": new (params: Json) => Resource<GraphCollections>;
  "authors-posts": new (params: Json) => Resource<GraphCollections>;
  "posts-comments": new (params: Json) => Resource<GraphCollections>;
};

export class PublishedPostsFilterMapper implements Mapper<PostId, PostValue, PostId, PostValue> {
  constructor() {
  }

  mapEntry(
    key: PostId,
    values: Values<PostValue>,
    _context: Context
  ): Iterable<[PostId, PostValue]> {
    const result: Array<[PostId, PostValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.published === 1) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class PostsByAuthorFilterMapper implements Mapper<PostId, PostValue, PostId, PostValue> {
  private authorId: string;

  constructor(authorId: string) {
    this.authorId = authorId;
  }

  mapEntry(
    key: PostId,
    values: Values<PostValue>,
    _context: Context
  ): Iterable<[PostId, PostValue]> {
    const result: Array<[PostId, PostValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.authorId === this.authorId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class CommentsByPostFilterMapper implements Mapper<CommentId, CommentValue, CommentId, CommentValue> {
  private postId: string;

  constructor(postId: string) {
    this.postId = postId;
  }

  mapEntry(
    key: CommentId,
    values: Values<CommentValue>,
    _context: Context
  ): Iterable<[CommentId, CommentValue]> {
    const result: Array<[CommentId, CommentValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.postId === this.postId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class AuthorsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AuthorId, AuthorValue> {
    return cs.authors;
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

export class PostsPublishedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PostId, PostValue> {
    return cs.posts.map(PublishedPostsFilterMapper);
  }
}

export class AuthorsPostsResource implements Resource<GraphCollections> {
  private authorId: string;

  constructor(params: Json) {
    const typed = params as AuthorsPostsResourceParams;
    this.authorId = typed.authorId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PostId, PostValue> {
    return cs.posts.map(PostsByAuthorFilterMapper, this.authorId);
  }
}

export class PostsCommentsResource implements Resource<GraphCollections> {
  private postId: string;

  constructor(params: Json) {
    const typed = params as PostsCommentsResourceParams;
    this.postId = typed.postId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CommentId, CommentValue> {
    return cs.comments.map(CommentsByPostFilterMapper, this.postId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyAuthors: Entry<AuthorId, AuthorValue>[] = Array.of();
    const emptyPosts: Entry<PostId, PostValue>[] = Array.of();
    const emptyComments: Entry<CommentId, CommentValue>[] = Array.of();
    this.initialData = { authors: emptyAuthors, posts: emptyPosts, comments: emptyComments };
    this.resources = { "authors": AuthorsResource, "posts": PostsResource, "posts-published": PostsPublishedResource, "authors-posts": AuthorsPostsResource, "posts-comments": PostsCommentsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { authors: inputs.authors, posts: inputs.posts, comments: inputs.comments };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
