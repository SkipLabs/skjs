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

export type GetNotificationParams = { readonly notificationId: string } & {
  readonly [key: string]: Json | null;
};

export type IngestNotificationEventRequest = {
  readonly actorUserId: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
} & { readonly [key: string]: Json | null };

export type IngestNotificationEventRequest_skip_id_ = {
  readonly actorUserId: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
} & { readonly [key: string]: Json | null };

export type IngestNotificationEventRequest_skip_value_ = {
  readonly actorUserId: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
} & { readonly [key: string]: Json | null };

export type ListNotificationEventsParams = {
  readonly notificationId: string;
} & { readonly [key: string]: Json | null };

export type MarkAllReadResult = { readonly updatedCount: number } & {
  readonly [key: string]: Json | null;
};

export type MarkAllReadResult_skip_id_ = { readonly updatedCount: number } & {
  readonly [key: string]: Json | null;
};

export type MarkAllReadResult_skip_value_ = {
  readonly updatedCount: number;
} & { readonly [key: string]: Json | null };

export type Notification = {
  readonly createdAt: string;
  readonly eventCount: number;
  readonly firstEventAt: string;
  readonly id: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recentActorUserIds: string[];
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type NotificationEvent = {
  readonly actorUserId: string;
  readonly createdAt: string;
  readonly eventId: string;
  readonly notificationId: string;
} & { readonly [key: string]: Json | null };

export type NotificationEventCompositeKey = {
  readonly eventId: string;
  readonly notificationId: string;
} & { readonly [key: string]: Json | null };

export type NotificationEventList = { readonly events: NotificationEvent[] } & {
  readonly [key: string]: Json | null;
};

export type NotificationEventList_skip_id_ = {
  readonly events: NotificationEvent[];
} & { readonly [key: string]: Json | null };

export type NotificationEventList_skip_value_ = {
  readonly events: NotificationEvent[];
} & { readonly [key: string]: Json | null };

export type NotificationEventStored = {
  readonly actorUserId: string;
  readonly createdAt: string;
} & { readonly [key: string]: Json | null };

export type NotificationEventStoredWithEventId = {
  readonly actorUserId: string;
  readonly createdAt: string;
  readonly eventId: string;
} & { readonly [key: string]: Json | null };

export type NotificationEvent_skip_id_ = {
  readonly eventId: string;
  readonly notificationId: string;
} & { readonly [key: string]: Json | null };

export type NotificationEvent_skip_value_ = {
  readonly actorUserId: string;
  readonly createdAt: string;
} & { readonly [key: string]: Json | null };

export type NotificationList = { readonly notifications: Notification[] } & {
  readonly [key: string]: Json | null;
};

export type NotificationList_skip_id_ = {
  readonly notifications: Notification[];
} & { readonly [key: string]: Json | null };

export type NotificationList_skip_value_ = {
  readonly notifications: Notification[];
} & { readonly [key: string]: Json | null };

export type NotificationStored = {
  readonly createdAt: string;
  readonly eventCount: number;
  readonly firstEventAt: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type NotificationType = "MENTION" | "FOLLOW" | "LIKE";

export type NotificationType_skip_id_ = "MENTION" | "FOLLOW" | "LIKE";

export type NotificationType_skip_value_ = "MENTION" | "FOLLOW" | "LIKE";

export type Notification_skip_id_ = string;

export type Notification_skip_value_ = {
  readonly createdAt: string;
  readonly eventCount: number;
  readonly firstEventAt: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recentActorUserIds: string[];
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly type: NotificationType;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type UnreadCount = { readonly count: number } & {
  readonly [key: string]: Json | null;
};

export type UnreadTally = number;

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
