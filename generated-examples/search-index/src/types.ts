import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CreatePostRequest = {
  readonly body: string;
  readonly tagIds?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreatePostRequest_skip_id_ = {
  readonly body: string;
  readonly tagIds?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreatePostRequest_skip_value_ = {
  readonly body: string;
  readonly tagIds?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateTagRequest = { readonly name: string } & {
  readonly [key: string]: Json | null;
};

export type CreateTagRequest_skip_id_ = { readonly name: string } & {
  readonly [key: string]: Json | null;
};

export type CreateTagRequest_skip_value_ = { readonly name: string } & {
  readonly [key: string]: Json | null;
};

export type Post = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly tagIds?: string[];
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type PostIdKey = string;

export type PostList = { readonly items: Post[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type PostList_skip_id_ = {
  readonly items: Post[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PostList_skip_value_ = {
  readonly items: Post[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PostStored = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type PostTag = {
  readonly createdAt: string;
  readonly postId: string;
  readonly tagId: string;
} & { readonly [key: string]: Json | null };

export type PostTagKey = { readonly postId: string; readonly tagId: string } & {
  readonly [key: string]: Json | null;
};

export type PostTagList = {
  readonly items: PostTag[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PostTagList_skip_id_ = {
  readonly items: PostTag[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PostTagList_skip_value_ = {
  readonly items: PostTag[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PostTagStored = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type PostTag_skip_id_ = {
  readonly postId: string;
  readonly tagId: string;
} & { readonly [key: string]: Json | null };

export type PostTag_skip_value_ = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly tagIds?: string[];
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type SearchDocument = {
  readonly authorDisplayName?: string;
  readonly authorId: string;
  readonly authorUsername?: string;
  readonly body: string;
  readonly createdAt: string;
  readonly postId: string;
  readonly searchText: string;
  readonly tagNames: string[];
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type SearchDocumentList = {
  readonly items: SearchDocument[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SearchDocumentList_skip_id_ = {
  readonly items: SearchDocument[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SearchDocumentList_skip_value_ = {
  readonly items: SearchDocument[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SearchDocumentStored = {
  readonly authorId: string;
  readonly postId: string;
} & { readonly [key: string]: Json | null };

export type SearchDocument_skip_id_ = {
  readonly authorDisplayName?: string;
  readonly authorId: string;
  readonly authorUsername?: string;
  readonly body: string;
  readonly createdAt: string;
  readonly postId: string;
  readonly searchText: string;
  readonly tagNames: string[];
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type SearchDocument_skip_value_ = {
  readonly authorDisplayName?: string;
  readonly authorId: string;
  readonly authorUsername?: string;
  readonly body: string;
  readonly createdAt: string;
  readonly postId: string;
  readonly searchText: string;
  readonly tagNames: string[];
  readonly title: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Tag = {
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type TagIdKey = string;

export type TagList = { readonly items: Tag[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type TagList_skip_id_ = {
  readonly items: Tag[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type TagList_skip_value_ = {
  readonly items: Tag[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type TagNameLowerKey = string;

export type Tag_skip_id_ = string;

export type Tag_skip_value_ = {
  readonly createdAt: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest = {
  readonly body?: string;
  readonly tagIds?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest_skip_id_ = {
  readonly body?: string;
  readonly tagIds?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest_skip_value_ = {
  readonly body?: string;
  readonly tagIds?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTagRequest = { readonly name?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateTagRequest_skip_id_ = { readonly name?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateTagRequest_skip_value_ = { readonly name?: string } & {
  readonly [key: string]: Json | null;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly updatedAt?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly updatedAt?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
