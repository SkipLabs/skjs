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

export type Comment = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly postId: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type CommentCount = number;

export type CommentList = {
  readonly items: Comment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type CommentList_skip_id_ = {
  readonly items: Comment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type CommentList_skip_value_ = {
  readonly items: Comment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Comment_skip_id_ = string;

export type Comment_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly postId: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type CreateCommentRequest = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreateCommentRequest_skip_id_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreateCommentRequest_skip_value_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePostRequest = {
  readonly body: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreatePostRequest_skip_id_ = {
  readonly body: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreatePostRequest_skip_value_ = {
  readonly body: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type ListPostsParams = {
  readonly authorId?: string;
  readonly status?: PostStatus;
  readonly tag?: string;
} & { readonly [key: string]: Json | null };

export type Post = {
  readonly authorId: string;
  readonly body: string;
  readonly commentCount?: number;
  readonly createdAt: string;
  readonly id: string;
  readonly publishedAt?: string;
  readonly status: PostStatus;
  readonly tags: string[];
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

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

export type PostStatus = "DRAFT" | "PUBLISHED" | "ARCHIVED";

export type PostStatus_skip_id_ = "DRAFT" | "PUBLISHED" | "ARCHIVED";

export type PostStatus_skip_value_ = "DRAFT" | "PUBLISHED" | "ARCHIVED";

export type PostStored = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly publishedAt?: string;
  readonly status: PostStatus;
  readonly tags: string[];
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly commentCount?: number;
  readonly createdAt: string;
  readonly publishedAt?: string;
  readonly status: PostStatus;
  readonly tags: string[];
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type UpdateCommentRequest = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateCommentRequest_skip_id_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateCommentRequest_skip_value_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest = {
  readonly body?: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest_skip_id_ = {
  readonly body?: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePostRequest_skip_value_ = {
  readonly body?: string;
  readonly status?: PostStatus;
  readonly tags?: string[];
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
