// === User Types ===
export type UserId = string;

export type UserValue = {
  username: string;
  displayName: string;
  bio: string | null;
};

// API type with id (provided by client, NEVER generated)
export type User = UserValue & { id: UserId };

// === Post Types ===
export type PostId = string;

export type PostValue = {
  authorId: string;
  title: string;
  content: string;
  createdAt: number;
};

// API type with id (provided by client, NEVER generated)
export type Post = PostValue & { id: PostId };

// === Tag Types ===
export type TagId = string;

export type TagValue = {
  name: string;
  description: string | null;
};

// API type with id (provided by client, NEVER generated)
export type Tag = TagValue & { id: TagId };

// === PostTag Types ===
export type PostTagId = string;

export type PostTagValue = {
  postId: string;
  tagId: string;
};

// === SearchDocument Types ===
export type SearchDocumentId = string;

export type SearchDocumentValue = {
  postId: string;
  title: string;
  content: string;
  createdAt: number;
  authorId: string;
  authorUsername: string;
  authorDisplayName: string;
  tagNames: Array<string>;
};
