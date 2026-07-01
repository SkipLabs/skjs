export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type Comment = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly postId: string;
};

export type CommentList = { readonly comments: Comment[] };

export type CommentList_skip_id_ = { readonly comments: Comment[] };

export type CommentList_skip_value_ = { readonly comments: Comment[] };

export type Comment_skip_id_ = string;

export type Comment_skip_value_ = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly postId: string;
};

export type CreateCommentRequest = { readonly content: string };

export type CreateCommentRequest_skip_id_ = { readonly content: string };

export type CreateCommentRequest_skip_value_ = { readonly content: string };

export type CreatePostRequest = { readonly content: string };

export type CreatePostRequest_skip_id_ = { readonly content: string };

export type CreatePostRequest_skip_value_ = { readonly content: string };

export type Feed = { readonly items: FeedItem[] };

export type FeedItem = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly kind: FeedItemKind;
  readonly occurredAt: string;
  readonly postId: string;
};

export type FeedItemKey = {
  readonly commentId?: string;
  readonly kind: "post" | "like" | "comment";
  readonly postId: string;
  readonly userId?: string;
};

export type FeedItemKind = "post" | "like" | "comment";

export type FeedItemKind_skip_id_ = "post" | "like" | "comment";

export type FeedItemKind_skip_value_ = "post" | "like" | "comment";

export type FeedItem_skip_id_ = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly kind: FeedItemKind;
  readonly occurredAt: string;
  readonly postId: string;
};

export type FeedItem_skip_value_ = {
  readonly actorId: string;
  readonly commentId?: string;
  readonly kind: FeedItemKind;
  readonly occurredAt: string;
  readonly postId: string;
};

export type Feed_skip_id_ = { readonly items: FeedItem[] };

export type Feed_skip_value_ = { readonly items: FeedItem[] };

export type GetCommentByIdParams = { readonly commentId: string };

export type GetPostByIdParams = { readonly postId: string };

export type Like = {
  readonly createdAt: string;
  readonly postId: string;
  readonly userId: string;
};

export type LikeKey = { readonly postId: string; readonly userId: string };

export type LikeList = { readonly likes: Like[] };

export type LikeList_skip_id_ = { readonly likes: Like[] };

export type LikeList_skip_value_ = { readonly likes: Like[] };

export type LikeStored = { readonly createdAt: string };

export type Like_skip_id_ = {
  readonly postId: string;
  readonly userId: string;
};

export type Like_skip_value_ = { readonly createdAt: string };

export type ListPostsParams = { readonly authorId?: string };

export type Post = {
  readonly authorId: string;
  readonly commentCount: number;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly likeCount: number;
  readonly updatedAt?: string;
};

export type PostCommentCount = number;

export type PostCommentCountAccum = number;

export type PostLikeCount = number;

export type PostLikeCountAccum = number;

export type PostList = { readonly posts: Post[] };

export type PostList_skip_id_ = { readonly posts: Post[] };

export type PostList_skip_value_ = { readonly posts: Post[] };

export type PostStored = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly updatedAt?: string;
};

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly commentCount: number;
  readonly content: string;
  readonly createdAt: string;
  readonly likeCount: number;
  readonly updatedAt?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdatePostRequest = { readonly content?: string };

export type UpdatePostRequest_skip_id_ = { readonly content?: string };

export type UpdatePostRequest_skip_value_ = { readonly content?: string };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
};
