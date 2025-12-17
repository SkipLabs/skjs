export type PostCommentEnum = "post" | "comment";

export type PostLikeCommentEnum = "post" | "like" | "comment";

export type PostId = string;

export type PostValue = {
  authorId: string;
  content: string;
  timestamp: number;
};

export type Post = PostValue & { id: PostId };

export type LikeId = string;

export type LikeValue = {
  userId: string;
  targetId: string;
  targetType: PostCommentEnum;
  timestamp: number;
};

export type Like = LikeValue & { id: LikeId };

export type CommentId = string;

export type CommentValue = {
  authorId: string;
  postId: string;
  content: string;
  timestamp: number;
};

export type Comment = CommentValue & { id: CommentId };

export type FeedItemId = string;

export type FeedItemValue = {
  itemType: PostLikeCommentEnum;
  authorId: string;
  content: string | null;
  targetId: string | null;
  targetType: string | null;
  postId: string | null;
  timestamp: number;
};

export type FeedItem = FeedItemValue & { id: FeedItemId };
