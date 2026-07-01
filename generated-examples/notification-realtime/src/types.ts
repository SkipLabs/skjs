import type { Json } from "@skipruntime/core";

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

export type CreateNotificationRequest = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly title: string;
  readonly type: NotificationType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type CreateNotificationRequest_skip_id_ = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly title: string;
  readonly type: NotificationType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type CreateNotificationRequest_skip_value_ = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly title: string;
  readonly type: NotificationType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Created = "created";

export type Created_skip_id_ = "created";

export type Created_skip_value_ = "created";

export type GetNotificationParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListNotificationsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type MarkAllReadResponse = { readonly updatedCount: number } & {
  readonly [key: string]: Json | null;
};

export type MarkAllReadResponse_skip_id_ = { readonly updatedCount: number } & {
  readonly [key: string]: Json | null;
};

export type MarkAllReadResponse_skip_value_ = {
  readonly updatedCount: number;
} & { readonly [key: string]: Json | null };

export type Notification = {
  readonly body?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly linkUrl?: string;
  readonly readAt?: string;
  readonly title: string;
  readonly type: NotificationType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type NotificationEvent = {
  readonly eventType: Created;
  readonly notification: Notification;
} & { readonly [key: string]: Json | null };

export type NotificationEvent_skip_id_ = {
  readonly eventType: Created;
  readonly notification: Notification;
} & { readonly [key: string]: Json | null };

export type NotificationEvent_skip_value_ = {
  readonly eventType: Created;
  readonly notification: Notification;
} & { readonly [key: string]: Json | null };

export type NotificationList = {
  readonly notifications: Notification[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type NotificationList_skip_id_ = {
  readonly notifications: Notification[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type NotificationList_skip_value_ = {
  readonly notifications: Notification[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type NotificationType =
  | "INFO"
  | "SUCCESS"
  | "WARNING"
  | "ERROR"
  | "MENTION"
  | "SYSTEM";

export type NotificationType_skip_id_ =
  | "INFO"
  | "SUCCESS"
  | "WARNING"
  | "ERROR"
  | "MENTION"
  | "SYSTEM";

export type NotificationType_skip_value_ =
  | "INFO"
  | "SUCCESS"
  | "WARNING"
  | "ERROR"
  | "MENTION"
  | "SYSTEM";

export type Notification_skip_id_ = string;

export type Notification_skip_value_ = {
  readonly body?: string;
  readonly createdAt: string;
  readonly linkUrl?: string;
  readonly readAt?: string;
  readonly title: string;
  readonly type: NotificationType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type UnreadCount = number;

export type UnreadCountParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type UnreadCountResponse = { readonly unreadCount: number } & {
  readonly [key: string]: Json | null;
};

export type UnreadCountResponse_skip_id_ = { readonly unreadCount: number } & {
  readonly [key: string]: Json | null;
};

export type UnreadCountResponse_skip_value_ = {
  readonly unreadCount: number;
} & { readonly [key: string]: Json | null };

export type UnreadOne = number;

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
