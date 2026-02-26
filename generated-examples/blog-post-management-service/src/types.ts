export type AuthorId = string;

export type AuthorValue = {
  name: string;
  email: string;
  bio: string | null;
};

export type Author = AuthorValue & { id: AuthorId };

export type PostId = string;

export type PostValue = {
  authorId: string;
  title: string;
  content: string;
  createdAt: number;
  updatedAt: number;
  published: number;
  tags: string;
};

export type Post = PostValue & { id: PostId };

export type CommentId = string;

export type CommentValue = {
  postId: string;
  authorId: string;
  content: string;
  createdAt: number;
};

export type Comment = CommentValue & { id: CommentId };

export type AuthorsPostsResourceParams = {
  authorId: string;
};

export type PostsCommentsResourceParams = {
  postId: string;
};
