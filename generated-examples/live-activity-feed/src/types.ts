import type { Json } from "@skipruntime/core";

export type Activity = {
  readonly authorId: string;
  readonly createdAt: string;
  readonly id: string;
  readonly message: string;
  readonly targetUrl?: string;
  readonly type: ActivityType;
} & { readonly [key: string]: Json | null };

export type ActivityEvent = { readonly activity: Activity } & {
  readonly [key: string]: Json | null;
};

export type ActivityEvent_skip_id_ = { readonly activity: Activity } & {
  readonly [key: string]: Json | null;
};

export type ActivityEvent_skip_value_ = { readonly activity: Activity } & {
  readonly [key: string]: Json | null;
};

export type ActivityList = {
  readonly items: Activity[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type ActivityList_skip_id_ = {
  readonly items: Activity[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type ActivityList_skip_value_ = {
  readonly items: Activity[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type ActivityType = "post" | "comment" | "like" | "share" | "milestone";

export type ActivityType_skip_id_ =
  | "post"
  | "comment"
  | "like"
  | "share"
  | "milestone";

export type ActivityType_skip_value_ =
  | "post"
  | "comment"
  | "like"
  | "share"
  | "milestone";

export type Activity_skip_id_ = string;

export type Activity_skip_value_ = {
  readonly authorId: string;
  readonly createdAt: string;
  readonly message: string;
  readonly targetUrl?: string;
  readonly type: ActivityType;
} & { readonly [key: string]: Json | null };

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

export type CreateActivityRequest = {
  readonly message: string;
  readonly targetUrl?: string;
  readonly type: ActivityType;
} & { readonly [key: string]: Json | null };

export type CreateActivityRequest_skip_id_ = {
  readonly message: string;
  readonly targetUrl?: string;
  readonly type: ActivityType;
} & { readonly [key: string]: Json | null };

export type CreateActivityRequest_skip_value_ = {
  readonly message: string;
  readonly targetUrl?: string;
  readonly type: ActivityType;
} & { readonly [key: string]: Json | null };

export type CreateFollowRequest = { readonly followeeId: string } & {
  readonly [key: string]: Json | null;
};

export type CreateFollowRequest_skip_id_ = { readonly followeeId: string } & {
  readonly [key: string]: Json | null;
};

export type CreateFollowRequest_skip_value_ = {
  readonly followeeId: string;
} & { readonly [key: string]: Json | null };

export type FeedScope = "following" | "global";

export type FeedScope_skip_id_ = "following" | "global";

export type FeedScope_skip_value_ = "following" | "global";

export type Follow = {
  readonly createdAt: string;
  readonly followeeId: string;
  readonly followerId: string;
} & { readonly [key: string]: Json | null };

export type FollowByFollowerValue = {
  readonly createdAt: string;
  readonly followeeId: string;
} & { readonly [key: string]: Json | null };

export type FollowList = {
  readonly items: Follow[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type FollowList_skip_id_ = {
  readonly items: Follow[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type FollowList_skip_value_ = {
  readonly items: Follow[];
  readonly limit?: number;
  readonly offset?: number;
} & { readonly [key: string]: Json | null };

export type FollowPairKey = {
  readonly followeeId: string;
  readonly followerId: string;
} & { readonly [key: string]: Json | null };

export type Follow_skip_id_ = {
  readonly followeeId: string;
  readonly followerId: string;
} & { readonly [key: string]: Json | null };

export type Follow_skip_value_ = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type ListActivitiesParams = {
  readonly authorId?: string;
  readonly scope?: string;
  readonly userId: string;
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

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
