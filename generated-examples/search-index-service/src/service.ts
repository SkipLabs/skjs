import type {
  EagerCollection,
  SkipService,
  Context,
  Mapper,
  Values,
  ResourceClass
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  UserId,
  UserValue,
  PostId,
  PostValue,
  TagId,
  TagValue,
  PostTagId,
  PostTagValue,
  SearchDocumentId,
  SearchDocumentValue,
} from "./types.js";

export type Inputs = {
  users: InputDefinition<UserId, UserValue>;
  posts: InputDefinition<PostId, PostValue>;
  tags: InputDefinition<TagId, TagValue>;
  postTags: InputDefinition<PostTagId, PostTagValue>;
};

export type InputCollections = {
  users: EagerCollection<UserId, UserValue>;
  posts: EagerCollection<PostId, PostValue>;
  tags: EagerCollection<TagId, TagValue>;
  postTags: EagerCollection<PostTagId, PostTagValue>;
};

export type GraphCollections = {
  users: EagerCollection<UserId, UserValue>;
  tags: EagerCollection<TagId, TagValue>;
  postTagsByPostId: EagerCollection<PostId, TagId>;
  searchDocuments: EagerCollection<SearchDocumentId, SearchDocumentValue>;
};

export type Resources = {};

export class PostTagsByPostIdMapper
  implements Mapper<PostTagId, PostTagValue, PostId, TagId>
{
  constructor() {}

  mapEntry(
    _key: PostTagId,
    values: Values<PostTagValue>,
    _context: Context
  ): Iterable<[PostId, TagId]> {
    const result: Array<[PostId, TagId]> = Array.of();
    for (const v of values) {
      result.push([v.postId, v.tagId]);
    }
    return result;
  }
}

export class SearchDocumentMapper
  implements Mapper<PostId, PostValue, SearchDocumentId, SearchDocumentValue>
{
  private users: EagerCollection<UserId, UserValue>;
  private postTagsByPostId: EagerCollection<PostId, TagId>;
  private tags: EagerCollection<TagId, TagValue>;

  constructor(
    users: EagerCollection<UserId, UserValue>,
    postTagsByPostId: EagerCollection<PostId, TagId>,
    tags: EagerCollection<TagId, TagValue>
  ) {
    this.users = users;
    this.postTagsByPostId = postTagsByPostId;
    this.tags = tags;
  }

  mapEntry(
    key: PostId,
    values: Values<PostValue>,
    _context: Context
  ): Iterable<[SearchDocumentId, SearchDocumentValue]> {
    const result: Array<[SearchDocumentId, SearchDocumentValue]> = Array.of();
    for (const post of values) {
      const authorArr = this.users.getArray(post.authorId);
      if (authorArr.length === 0) {
        continue;
      }
      const author = authorArr[0];
      if (author !== undefined) {
        const tagIds = this.postTagsByPostId.getArray(key);
        const tagNames: Array<string> = Array.of();
        for (const tagId of tagIds) {
          const tagArr = this.tags.getArray(tagId);
          const tagEntry = tagArr[0];
          if (tagEntry !== undefined) {
            tagNames.push(tagEntry.name);
          }
        }
        const searchDoc: SearchDocumentValue = {
          postId: key,
          title: post.title,
          content: post.content,
          createdAt: post.createdAt,
          authorId: post.authorId,
          authorUsername: author.username,
          authorDisplayName: author.displayName,
          tagNames: tagNames,
        };
        result.push([key, searchDoc]);
      }
    }
    return result;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                    this.inputs = {
      users: new InputDefinition<UserId, UserValue>([]),
      posts: new InputDefinition<PostId, PostValue>([]),
      tags: new InputDefinition<TagId, TagValue>([]),
      postTags: new InputDefinition<PostTagId, PostTagValue>([]),
    };
    this.resources = {};
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const postTagsByPostId = inputs.postTags.map(PostTagsByPostIdMapper);
    const searchDocuments = inputs.posts.map(
      SearchDocumentMapper,
      inputs.users,
      postTagsByPostId,
      inputs.tags
    );
    return {
      users: inputs.users,
      tags: inputs.tags,
      postTagsByPostId: postTagsByPostId,
      searchDocuments: searchDocuments,
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
