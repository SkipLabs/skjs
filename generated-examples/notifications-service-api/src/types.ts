export type MentionFollowLikeEnum = "mention" | "follow" | "like";

export type MentionId = string;

export type MentionValue = {
  fromUserId: string;
  toUserId: string;
  postId: string;
  timestamp: number;
};

export type Mention = MentionValue & { id: MentionId };

export type FollowId = string;

export type FollowValue = {
  fromUserId: string;
  toUserId: string;
  timestamp: number;
};

export type Follow = FollowValue & { id: FollowId };

export type LikeId = string;

export type LikeValue = {
  fromUserId: string;
  toUserId: string;
  postId: string;
  timestamp: number;
};

export type Like = LikeValue & { id: LikeId };

export type NotificationId = string;

export type NotificationValue = {
  userId: string;
  type: MentionFollowLikeEnum;
  count: number;
  latestTimestamp: number;
  actorIds: string;
};

export type Notification = NotificationValue & { id: NotificationId };
