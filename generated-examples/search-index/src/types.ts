export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreatePostRequest = {
  readonly body: string;
  readonly tagIds: string[];
  readonly title: string;
};

export type CreatePostRequest_skip_id_ = {
  readonly body: string;
  readonly tagIds: string[];
  readonly title: string;
};

export type CreatePostRequest_skip_value_ = {
  readonly body: string;
  readonly tagIds: string[];
  readonly title: string;
};

export type CreateTagRequest = { readonly name: string };

export type CreateTagRequest_skip_id_ = { readonly name: string };

export type CreateTagRequest_skip_value_ = { readonly name: string };

export type ListPostsParams = { readonly authorId?: string };

export type ListTagsParams = { readonly namePrefix?: string };

export type Post = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly tagIds: string[];
  readonly title: string;
  readonly updatedAt: string;
};

export type PostList = {
  readonly items: Post[];
  readonly limit: number;
  readonly offset: number;
};

export type PostList_skip_id_ = {
  readonly items: Post[];
  readonly limit: number;
  readonly offset: number;
};

export type PostList_skip_value_ = {
  readonly items: Post[];
  readonly limit: number;
  readonly offset: number;
};

export type PostStored = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly tagIds: string[];
  readonly title: string;
  readonly updatedAt: string;
};

export type Post_skip_id_ = string;

export type Post_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly tagIds: string[];
  readonly title: string;
  readonly updatedAt: string;
};

export type SearchDocument = {
  readonly authorDisplayName?: string;
  readonly authorId: string;
  readonly authorUsername?: string;
  readonly body: string;
  readonly createdAt: string;
  readonly postId: string;
  readonly tagIds: string[];
  readonly tagNames: string[];
  readonly title: string;
  readonly updatedAt: string;
};

export type SearchDocumentList = {
  readonly items: SearchDocument[];
  readonly limit: number;
  readonly offset: number;
};

export type SearchDocumentList_skip_id_ = {
  readonly items: SearchDocument[];
  readonly limit: number;
  readonly offset: number;
};

export type SearchDocumentList_skip_value_ = {
  readonly items: SearchDocument[];
  readonly limit: number;
  readonly offset: number;
};

export type SearchDocument_skip_id_ = string;

export type SearchDocument_skip_value_ = {
  readonly authorDisplayName?: string;
  readonly authorId: string;
  readonly authorUsername?: string;
  readonly body: string;
  readonly createdAt: string;
  readonly tagIds: string[];
  readonly tagNames: string[];
  readonly title: string;
  readonly updatedAt: string;
};

export type SearchParams = {
  readonly authorId?: string;
  readonly q?: string;
  readonly tagName?: string;
};

export type SearchSortKey = {
  readonly createdAtNeg: number;
  readonly postId: string;
};

export type Tag = {
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
};

export type TagList = {
  readonly items: Tag[];
  readonly limit: number;
  readonly offset: number;
};

export type TagList_skip_id_ = {
  readonly items: Tag[];
  readonly limit: number;
  readonly offset: number;
};

export type TagList_skip_value_ = {
  readonly items: Tag[];
  readonly limit: number;
  readonly offset: number;
};

export type TagNameSortKey = { readonly id: string; readonly name: string };

export type Tag_skip_id_ = string;

export type Tag_skip_value_ = {
  readonly createdAt: string;
  readonly name: string;
  readonly ownerId: string;
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
  readonly body?: string;
  readonly tagIds?: string[];
  readonly title?: string;
};

export type UpdatePostRequest_skip_id_ = {
  readonly body?: string;
  readonly tagIds?: string[];
  readonly title?: string;
};

export type UpdatePostRequest_skip_value_ = {
  readonly body?: string;
  readonly tagIds?: string[];
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
