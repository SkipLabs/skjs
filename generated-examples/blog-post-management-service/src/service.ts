import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

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


export type Inputs = {
  authors: InputDefinition<AuthorId, AuthorValue>;
  posts: InputDefinition<PostId, PostValue>;
  comments: InputDefinition<CommentId, CommentValue>;
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

export type Resources = {
  "authors": ResourceClass<GraphCollections, {}>;
  "posts": ResourceClass<GraphCollections, {}>;
  "posts-published": ResourceClass<GraphCollections, {}>;
  "authors-posts": ResourceClass<GraphCollections, AuthorsPostsResourceParams>;
  "posts-comments": ResourceClass<GraphCollections, PostsCommentsResourceParams>;
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
    for (const v of values) {
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
    for (const v of values) {
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
    for (const v of values) {
      if (v.postId === this.postId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class AuthorsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AuthorId, AuthorValue> {
    return cs.authors;
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

export class PostsPublishedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
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

  constructor(params: AuthorsPostsResourceParams) {
    this.authorId = params.authorId;
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

  constructor(params: PostsCommentsResourceParams) {
    this.postId = params.postId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CommentId, CommentValue> {
    return cs.comments.map(CommentsByPostFilterMapper, this.postId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
                this.inputs = { authors: new InputDefinition<AuthorId, AuthorValue>([]), posts: new InputDefinition<PostId, PostValue>([]), comments: new InputDefinition<CommentId, CommentValue>([]) };
    this.resources = { "authors": AuthorsResource, "posts": PostsResource, "posts-published": PostsPublishedResource, "authors-posts": AuthorsPostsResource, "posts-comments": PostsCommentsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { authors: inputs.authors, posts: inputs.posts, comments: inputs.comments };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
