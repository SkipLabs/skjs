export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Comment = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly postId: string;
};

export type CommentList = {
  readonly comments: Comment[];
  readonly total: number;
};

export type CommentList_skip_id_ = {
  readonly comments: Comment[];
  readonly total: number;
};

export type CommentList_skip_value_ = {
  readonly comments: Comment[];
  readonly total: number;
};

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

export type CreatePostRequest = {
  readonly content: string;
  readonly tags?: string[];
  readonly title: string;
};

export type CreatePostRequest_skip_id_ = {
  readonly content: string;
  readonly tags?: string[];
  readonly title: string;
};

export type CreatePostRequest_skip_value_ = {
  readonly content: string;
  readonly tags?: string[];
  readonly title: string;
};

export type ListCommentsParams = { readonly postId: string };

export type ListPostsParams = {
  readonly authorId?: string;
  readonly status?: PostStatus;
  readonly tag?: string;
};

export type Post = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly publishedAt?: string;
  readonly status: PostStatus;
  readonly tags: string[];
  readonly title: string;
  readonly updatedAt?: string;
};

export type PostList = { readonly posts: Post[]; readonly total: number };

export type PostList_skip_id_ = {
  readonly posts: Post[];
  readonly total: number;
};

export type PostList_skip_value_ = {
  readonly posts: Post[];
  readonly total: number;
};

export type PostStatus = "DRAFT" | "PUBLISHED";

export type PostStatus_skip_id_ = "DRAFT" | "PUBLISHED";

export type PostStatus_skip_value_ = "DRAFT" | "PUBLISHED";

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly publishedAt?: string;
  readonly status: PostStatus;
  readonly tags: string[];
  readonly title: string;
  readonly updatedAt?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdatePostRequest = {
  readonly content?: string;
  readonly tags?: string[];
  readonly title?: string;
};

export type UpdatePostRequest_skip_id_ = {
  readonly content?: string;
  readonly tags?: string[];
  readonly title?: string;
};

export type UpdatePostRequest_skip_value_ = {
  readonly content?: string;
  readonly tags?: string[];
  readonly title?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};
