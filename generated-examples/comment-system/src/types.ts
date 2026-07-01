export type ApiError = { readonly code?: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
};

export type Comment = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly likeCount: number;
  readonly parentCommentId?: string;
  readonly threadKey: string;
  readonly updatedAt: string;
};

export type CommentLike = {
  readonly commentId: string;
  readonly createdAt: string;
  readonly userId: string;
};

export type CommentLikeList = { readonly likes: CommentLike[] };

export type CommentLikeList_skip_id_ = { readonly likes: CommentLike[] };

export type CommentLikeList_skip_value_ = { readonly likes: CommentLike[] };

export type CommentLike_skip_id_ = {
  readonly commentId: string;
  readonly userId: string;
};

export type CommentLike_skip_value_ = { readonly createdAt: string };

export type CommentList = { readonly comments: Comment[] };

export type CommentList_skip_id_ = { readonly comments: Comment[] };

export type CommentList_skip_value_ = { readonly comments: Comment[] };

export type CommentStored = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly parentCommentId?: string;
  readonly threadKey: string;
  readonly updatedAt: string;
};

export type CommentWithLikeCount = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly likeCount: number;
  readonly parentCommentId?: string;
  readonly threadKey: string;
  readonly updatedAt: string;
};

export type Comment_skip_id_ = string;

export type Comment_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly likeCount: number;
  readonly parentCommentId?: string;
  readonly threadKey: string;
  readonly updatedAt: string;
};

export type CreateCommentRequest = {
  readonly body: string;
  readonly parentCommentId?: string;
  readonly threadKey?: string;
};

export type CreateCommentRequest_skip_id_ = {
  readonly body: string;
  readonly parentCommentId?: string;
  readonly threadKey?: string;
};

export type CreateCommentRequest_skip_value_ = {
  readonly body: string;
  readonly parentCommentId?: string;
  readonly threadKey?: string;
};

export type GetCommentParams = { readonly commentId: string };

export type GetUserParams = { readonly userId: string };

export type LikeIncrement = number;

export type ThreadKey = string;

export type UpdateCommentRequest = { readonly body: string };

export type UpdateCommentRequest_skip_id_ = { readonly body: string };

export type UpdateCommentRequest_skip_value_ = { readonly body: string };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly id: string;
  readonly updatedAt: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly updatedAt: string;
};
