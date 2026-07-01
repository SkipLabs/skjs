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
  readonly likeCount: number;
  readonly parentCommentId?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type CommentLike = {
  readonly commentId: string;
  readonly createdAt: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type CommentLikeList = {
  readonly items: CommentLike[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentLikeList_skip_id_ = {
  readonly items: CommentLike[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentLikeList_skip_value_ = {
  readonly items: CommentLike[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentLike_skip_id_ = {
  readonly commentId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type CommentLike_skip_value_ = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type CommentList = {
  readonly items: Comment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentList_skip_id_ = {
  readonly items: Comment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentList_skip_value_ = {
  readonly items: Comment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CommentStored = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly parentCommentId?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Comment_skip_id_ = string;

export type Comment_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly likeCount: number;
  readonly parentCommentId?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type CreateCommentRequest = {
  readonly body: string;
  readonly parentCommentId?: string;
} & { readonly [key: string]: Json | null };

export type CreateCommentRequest_skip_id_ = {
  readonly body: string;
  readonly parentCommentId?: string;
} & { readonly [key: string]: Json | null };

export type CreateCommentRequest_skip_value_ = {
  readonly body: string;
  readonly parentCommentId?: string;
} & { readonly [key: string]: Json | null };

export type GetCommentParams = { readonly commentId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type LikeCount = number;

export type ListCommentLikesParams = { readonly commentId: string } & {
  readonly [key: string]: Json | null;
};

export type ListCommentsParams = {
  readonly authorId?: string;
  readonly parentCommentId?: string;
  readonly rootOnly?: boolean;
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

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
