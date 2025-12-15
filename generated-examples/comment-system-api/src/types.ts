export type CommentReplyEnum = "comment" | "reply";

export type CommentId = string;

export type CommentValue = {
  authorId: string;
  content: string;
  createdAt: number;
};

export type Comment = CommentValue & { id: CommentId };

export type ReplyId = string;

export type ReplyValue = {
  commentId: string;
  authorId: string;
  content: string;
  createdAt: number;
};

export type Reply = ReplyValue & { id: ReplyId };

export type LikeId = string;

export type LikeValue = {
  commentId: string;
  userId: string;
  createdAt: number;
};

export type Like = LikeValue & { id: LikeId };

export type CommentWithStatsId = string;

export type CommentWithStatsValue = {
  authorId: string;
  content: string;
  createdAt: number;
  replyCount: number;
  likeCount: number;
};

export type CommentWithStats = CommentWithStatsValue & { id: CommentWithStatsId };

export type FeedItemId = string;

export type FeedItemValue = {
  type: CommentReplyEnum;
  authorId: string;
  content: string;
  createdAt: number;
  parentId: string | null;
};

export type FeedItem = FeedItemValue & { id: FeedItemId };

export type RepliesByCommentResourceParams = {
  commentId: string;
};

export type LikesByCommentResourceParams = {
  commentId: string;
};
