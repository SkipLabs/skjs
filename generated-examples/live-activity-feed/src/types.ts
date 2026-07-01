import type { Json } from "@skipruntime/core";

export type Activity = {
  readonly authorId: string;
  readonly createdAt: string;
  readonly id: string;
  readonly message: string;
  readonly metadata?: ActivityMetadata;
  readonly targetUrl?: string;
  readonly type: ActivityType;
};

export type ActivityCreatedAtKey = number;

export type ActivityEvent = {
  readonly activity?: Activity;
  readonly activityId?: string;
  readonly emittedAt: string;
  readonly kind: ActivityEventKind;
};

export type ActivityEventKind = "created" | "deleted";

export type ActivityEventKind_skip_id_ = "created" | "deleted";

export type ActivityEventKind_skip_value_ = "created" | "deleted";

export type ActivityEvent_skip_id_ = {
  readonly activity?: Activity;
  readonly activityId?: string;
  readonly emittedAt: string;
  readonly kind: ActivityEventKind;
};

export type ActivityEvent_skip_value_ = {
  readonly activity?: Activity;
  readonly activityId?: string;
  readonly emittedAt: string;
  readonly kind: ActivityEventKind;
};

export type ActivityMetadata = Record<string, Json>;

export type ActivityMetadata_skip_id_ = Record<string, Json>;

export type ActivityMetadata_skip_value_ = Record<string, Json>;

export type ActivityPage = {
  readonly items: Activity[];
  readonly nextBefore?: string;
};

export type ActivityPage_skip_id_ = {
  readonly items: Activity[];
  readonly nextBefore?: string;
};

export type ActivityPage_skip_value_ = {
  readonly items: Activity[];
  readonly nextBefore?: string;
};

export type ActivityType =
  | "post"
  | "comment"
  | "like"
  | "follow"
  | "share"
  | "custom";

export type ActivityType_skip_id_ =
  | "post"
  | "comment"
  | "like"
  | "follow"
  | "share"
  | "custom";

export type ActivityType_skip_value_ =
  | "post"
  | "comment"
  | "like"
  | "follow"
  | "share"
  | "custom";

export type Activity_skip_id_ = string;

export type Activity_skip_value_ = {
  readonly authorId: string;
  readonly createdAt: string;
  readonly message: string;
  readonly metadata?: ActivityMetadata;
  readonly targetUrl?: string;
  readonly type: ActivityType;
};

export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateActivityRequest = {
  readonly message: string;
  readonly metadata?: CreateActivityRequestMetadata;
  readonly targetUrl?: string;
  readonly type: ActivityType;
};

export type CreateActivityRequestMetadata = Record<string, Json>;

export type CreateActivityRequestMetadata_skip_id_ = Record<string, Json>;

export type CreateActivityRequestMetadata_skip_value_ = Record<string, Json>;

export type CreateActivityRequest_skip_id_ = {
  readonly message: string;
  readonly metadata?: CreateActivityRequestMetadata;
  readonly targetUrl?: string;
  readonly type: ActivityType;
};

export type CreateActivityRequest_skip_value_ = {
  readonly message: string;
  readonly metadata?: CreateActivityRequestMetadata;
  readonly targetUrl?: string;
  readonly type: ActivityType;
};

export type GetActivityByIdParams = { readonly activityId: string };

export type GetUserByIdParams = { readonly userId: string };

export type ListActivitiesParams = {
  readonly authorId?: string;
  readonly type?: string;
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
