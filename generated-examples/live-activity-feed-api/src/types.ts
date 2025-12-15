export type PostCommentLikeEnum = "post" | "comment" | "like";

export type PostId = string;

export type PostValue = {
  authorId: string;
  content: string;
  createdAt: number;
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

export type LikeId = string;

export type LikeValue = {
  postId: string;
  userId: string;
  createdAt: number;
};

export type Like = LikeValue & { id: LikeId };

export type UserId = string;

export type UserValue = {
  name: string;
  avatarUrl: string | null;
};

export type User = UserValue & { id: UserId };

export type FeedItemId = string;

export type FeedItemValue = {
  type: PostCommentLikeEnum;
  actorId: string;
  targetId: string;
  content: string | null;
  timestamp: number;
};

export type FeedItem = FeedItemValue & { id: FeedItemId };
