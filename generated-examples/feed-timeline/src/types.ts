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
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly postId: string;
} & { readonly [key: string]: Json | null };

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

export type Comment_skip_id_ = string;

export type Comment_skip_value_ = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly postId: string;
} & { readonly [key: string]: Json | null };

export type CountAccum = number;

export type CountValue = number;

export type CreateCommentRequest = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreateCommentRequest_skip_id_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreateCommentRequest_skip_value_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePostRequest = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePostRequest_skip_id_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreatePostRequest_skip_value_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type FeedEvent = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly content?: string;
  readonly id: string;
  readonly occurredAt: string;
  readonly postId: string;
  readonly type: FeedEventType;
} & { readonly [key: string]: Json | null };

export type FeedEventId = string;

export type FeedEventType = "POST" | "LIKE" | "COMMENT";

export type FeedEventType_skip_id_ = "POST" | "LIKE" | "COMMENT";

export type FeedEventType_skip_value_ = "POST" | "LIKE" | "COMMENT";

export type FeedEvent_skip_id_ = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly content?: string;
  readonly id: string;
  readonly occurredAt: string;
  readonly postId: string;
  readonly type: FeedEventType;
} & { readonly [key: string]: Json | null };

export type FeedEvent_skip_value_ = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly content?: string;
  readonly id: string;
  readonly occurredAt: string;
  readonly postId: string;
  readonly type: FeedEventType;
} & { readonly [key: string]: Json | null };

export type FeedPage = {
  readonly items: FeedEvent[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type FeedPage_skip_id_ = {
  readonly items: FeedEvent[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type FeedPage_skip_value_ = {
  readonly items: FeedEvent[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type GetPostByIdParams = { readonly postId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserByIdParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Like = {
  readonly createdAt: string;
  readonly postId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type LikeList = { readonly items: Like[]; readonly total?: number } & {
  readonly [key: string]: Json | null;
};

export type LikeList_skip_id_ = {
  readonly items: Like[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type LikeList_skip_value_ = {
  readonly items: Like[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type Like_skip_id_ = {
  readonly postId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Like_skip_value_ = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type ListCommentsByPostParams = { readonly postId: string } & {
  readonly [key: string]: Json | null;
};

export type ListLikesByPostParams = { readonly postId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPostsParams = { readonly authorId?: string } & {
  readonly [key: string]: Json | null;
};

export type Post = {
  readonly authorId: string;
  readonly commentCount: number;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly likeCount: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type PostList = { readonly items: Post[]; readonly total?: number } & {
  readonly [key: string]: Json | null;
};

export type PostList_skip_id_ = {
  readonly items: Post[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type PostList_skip_value_ = {
  readonly items: Post[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type PostStored = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly commentCount: number;
  readonly content: string;
  readonly createdAt: string;
  readonly likeCount: number;
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

export type UpdatePostRequest = { readonly content?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdatePostRequest_skip_id_ = { readonly content?: string } & {
  readonly [key: string]: Json | null;
};

export type UpdatePostRequest_skip_value_ = { readonly content?: string } & {
  readonly [key: string]: Json | null;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
