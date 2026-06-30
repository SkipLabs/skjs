export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateNotificationRequest = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly recipientUserId: string;
  readonly title: string;
  readonly type: NotificationType;
};

export type CreateNotificationRequest_skip_id_ = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly recipientUserId: string;
  readonly title: string;
  readonly type: NotificationType;
};

export type CreateNotificationRequest_skip_value_ = {
  readonly body?: string;
  readonly linkUrl?: string;
  readonly recipientUserId: string;
  readonly title: string;
  readonly type: NotificationType;
};

export type GetNotificationParams = {
  readonly notificationId: string;
  readonly userId: string;
};

export type GetUserByIdParams = { readonly userId: string };

export type ListNotificationsParams = {
  readonly since?: string;
  readonly status?: NotificationStatus;
  readonly userId: string;
};

export type MarkAllReadResult = { readonly markedCount: number };

export type MarkAllReadResult_skip_id_ = { readonly markedCount: number };

export type MarkAllReadResult_skip_value_ = { readonly markedCount: number };

export type Notification = {
  readonly body?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly linkUrl?: string;
  readonly readAt?: string;
  readonly recipientUserId: string;
  readonly senderUserId: string;
  readonly status: NotificationStatus;
  readonly title: string;
  readonly type: NotificationType;
};

export type NotificationByRecipientCreatedKey = {
  readonly id: string;
  readonly negCreatedAt: number;
  readonly recipientUserId: string;
};

export type NotificationEvent = {
  readonly eventType: NotificationEventType;
  readonly notification?: Notification;
  readonly notificationId: string;
  readonly occurredAt: string;
};

export type NotificationEventType = "created" | "read" | "deleted";

export type NotificationEventType_skip_id_ = "created" | "read" | "deleted";

export type NotificationEventType_skip_value_ = "created" | "read" | "deleted";

export type NotificationEvent_skip_id_ = {
  readonly eventType: NotificationEventType;
  readonly notification?: Notification;
  readonly notificationId: string;
  readonly occurredAt: string;
};

export type NotificationEvent_skip_value_ = {
  readonly eventType: NotificationEventType;
  readonly notification?: Notification;
  readonly notificationId: string;
  readonly occurredAt: string;
};

export type NotificationList = {
  readonly items: Notification[];
  readonly total: number;
};

export type NotificationList_skip_id_ = {
  readonly items: Notification[];
  readonly total: number;
};

export type NotificationList_skip_value_ = {
  readonly items: Notification[];
  readonly total: number;
};

export type NotificationStatus = "UNREAD" | "READ";

export type NotificationStatus_skip_id_ = "UNREAD" | "READ";

export type NotificationStatus_skip_value_ = "UNREAD" | "READ";

export type NotificationType =
  | "INFO"
  | "MENTION"
  | "FOLLOW"
  | "MESSAGE"
  | "SYSTEM"
  | "ALERT";

export type NotificationType_skip_id_ =
  | "INFO"
  | "MENTION"
  | "FOLLOW"
  | "MESSAGE"
  | "SYSTEM"
  | "ALERT";

export type NotificationType_skip_value_ =
  | "INFO"
  | "MENTION"
  | "FOLLOW"
  | "MESSAGE"
  | "SYSTEM"
  | "ALERT";

export type Notification_skip_id_ = string;

export type Notification_skip_value_ = {
  readonly body?: string;
  readonly createdAt: string;
  readonly linkUrl?: string;
  readonly readAt?: string;
  readonly recipientUserId: string;
  readonly senderUserId: string;
  readonly status: NotificationStatus;
  readonly title: string;
  readonly type: NotificationType;
};

export type RecipientUserIdKey = string;

export type UnreadCount = { readonly count: number };

export type UnreadCountParams = { readonly userId: string };

export type UnreadCount_skip_id_ = { readonly count: number };

export type UnreadCount_skip_value_ = { readonly count: number };

export type UnreadMarker = number;

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};
