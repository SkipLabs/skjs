export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type GetMyNotificationParams = {
  readonly notificationId: string;
  readonly userId: string;
};

export type IngestNotificationEventRequest = {
  readonly recipientUserId: string;
  readonly snippet?: string;
  readonly targetId: string;
  readonly targetType: TargetType;
  readonly type: NotificationType;
};

export type IngestNotificationEventRequest_skip_id_ = {
  readonly recipientUserId: string;
  readonly snippet?: string;
  readonly targetId: string;
  readonly targetType: TargetType;
  readonly type: NotificationType;
};

export type IngestNotificationEventRequest_skip_value_ = {
  readonly recipientUserId: string;
  readonly snippet?: string;
  readonly targetId: string;
  readonly targetType: TargetType;
  readonly type: NotificationType;
};

export type ListMyNotificationsParams = {
  readonly type?: "mention" | "follow" | "like";
  readonly unreadOnly?: boolean;
  readonly userId: string;
};

export type ListNotificationEventsParams = { readonly notificationId: string };

export type MarkAllReadResult = { readonly updatedCount: number };

export type MarkAllReadResult_skip_id_ = { readonly updatedCount: number };

export type MarkAllReadResult_skip_value_ = { readonly updatedCount: number };

export type Notification = {
  readonly actorCount: number;
  readonly createdAt: string;
  readonly eventCount: number;
  readonly id: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recentActorUserIds: string[];
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly targetType: TargetType;
  readonly type: NotificationType;
};

export type NotificationByRecipientValue = {
  readonly createdAt: string;
  readonly id: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly targetType: "user" | "post" | "comment";
  readonly type: "mention" | "follow" | "like";
};

export type NotificationEvent = {
  readonly actorUserId: string;
  readonly id: string;
  readonly notificationId: string;
  readonly occurredAt: string;
  readonly snippet?: string;
};

export type NotificationEventChild = {
  readonly actorUserId: string;
  readonly id: string;
  readonly notificationId: string;
  readonly occurredAt: string;
  readonly snippet?: string;
};

export type NotificationEventKey = {
  readonly id: string;
  readonly notificationId: string;
};

export type NotificationEventPage = {
  readonly events: NotificationEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total?: number;
};

export type NotificationEventPage_skip_id_ = {
  readonly events: NotificationEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total?: number;
};

export type NotificationEventPage_skip_value_ = {
  readonly events: NotificationEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total?: number;
};

export type NotificationEventValue = {
  readonly actorUserId: string;
  readonly occurredAt: string;
  readonly snippet?: string;
};

export type NotificationEvent_skip_id_ = {
  readonly id: string;
  readonly notificationId: string;
};

export type NotificationEvent_skip_value_ = {
  readonly actorUserId: string;
  readonly occurredAt: string;
  readonly snippet?: string;
};

export type NotificationFull = {
  readonly actorCount: number;
  readonly createdAt: string;
  readonly eventCount: number;
  readonly id: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recentActorUserIds: string[];
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly targetType: "user" | "post" | "comment";
  readonly type: "mention" | "follow" | "like";
};

export type NotificationPage = {
  readonly limit: number;
  readonly notifications: Notification[];
  readonly offset: number;
  readonly total?: number;
};

export type NotificationPage_skip_id_ = {
  readonly limit: number;
  readonly notifications: Notification[];
  readonly offset: number;
  readonly total?: number;
};

export type NotificationPage_skip_value_ = {
  readonly limit: number;
  readonly notifications: Notification[];
  readonly offset: number;
  readonly total?: number;
};

export type NotificationStored = {
  readonly createdAt: string;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly targetType: "user" | "post" | "comment";
  readonly type: "mention" | "follow" | "like";
};

export type NotificationType = "mention" | "follow" | "like";

export type NotificationType_skip_id_ = "mention" | "follow" | "like";

export type NotificationType_skip_value_ = "mention" | "follow" | "like";

export type Notification_skip_id_ = string;

export type Notification_skip_value_ = {
  readonly actorCount: number;
  readonly createdAt: string;
  readonly eventCount: number;
  readonly lastEventAt: string;
  readonly readAt?: string;
  readonly recentActorUserIds: string[];
  readonly recipientUserId: string;
  readonly targetId: string;
  readonly targetType: TargetType;
  readonly type: NotificationType;
};

export type RecipientUserId = string;

export type TargetType = "user" | "post" | "comment";

export type TargetType_skip_id_ = "user" | "post" | "comment";

export type TargetType_skip_value_ = "user" | "post" | "comment";

export type UnreadCount = { readonly count: number };

export type UnreadCountAccum = number;

export type UnreadCountParams = { readonly userId: string };

export type UnreadCountValue = number;

export type UnreadCount_skip_id_ = { readonly count: number };

export type UnreadCount_skip_value_ = { readonly count: number };

export type UpdateNotificationRequest = { readonly read: boolean };

export type UpdateNotificationRequest_skip_id_ = { readonly read: boolean };

export type UpdateNotificationRequest_skip_value_ = { readonly read: boolean };
