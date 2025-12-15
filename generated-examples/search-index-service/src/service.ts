import type {
  EagerCollection,
  Entry,
  SkipService,
  Context,
  Mapper,
  Values,
} from "@skipruntime/core";

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

type Inputs = {
  users: Entry<UserId, UserValue>[];
  posts: Entry<PostId, PostValue>[];
  tags: Entry<TagId, TagValue>[];
  postTags: Entry<PostTagId, PostTagValue>[];
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

type Resources = {};

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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const post = arr[i]!;
      const authorArr = this.users.getArray(post.authorId);
      if (authorArr.length === 0) {
        continue;
      }
      const author = authorArr[0]!;
      const tagIds = this.postTagsByPostId.getArray(key);
      const tagNames: Array<string> = Array.of();
      for (let j = 0; j < tagIds.length; j++) {
        const tagId = tagIds[j]!;
        const tagArr = this.tags.getArray(tagId);
        if (tagArr.length > 0) {
          tagNames.push(tagArr[0]!.name);
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
    return result;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyUsers: Entry<UserId, UserValue>[] = Array.of();
    const emptyPosts: Entry<PostId, PostValue>[] = Array.of();
    const emptyTags: Entry<TagId, TagValue>[] = Array.of();
    const emptyPostTags: Entry<PostTagId, PostTagValue>[] = Array.of();
    this.initialData = {
      users: emptyUsers,
      posts: emptyPosts,
      tags: emptyTags,
      postTags: emptyPostTags,
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
