export type InfoWarningErrorSuccessEnum = "info" | "warning" | "error" | "success";

export type NotificationId = string;

export type NotificationValue = {
  userId: string;
  title: string;
  message: string;
  type: InfoWarningErrorSuccessEnum;
  read: number;
  createdAt: number;
  updatedAt: number | null;
};

export type Notification = NotificationValue & { id: NotificationId };

export type NotificationsUserResourceParams = {
  userId: string;
};
