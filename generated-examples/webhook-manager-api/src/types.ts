export type PendingSuccessFailedEnum = "pending" | "success" | "failed";

export type WebhookId = string;

export type WebhookValue = {
  name: string;
  url: string;
  eventTypes: string;
  enabled: number;
  createdAt: number;
  secret: string | null;
};

export type Webhook = WebhookValue & { id: WebhookId };

export type DeliveryId = string;

export type DeliveryValue = {
  webhookId: string;
  eventType: string;
  payload: string;
  status: PendingSuccessFailedEnum;
  statusCode: number | null;
  attemptedAt: number;
  responseBody: string | null;
};

export type Delivery = DeliveryValue & { id: DeliveryId };

export type WebhookStatsId = string;

export type WebhookStatsValue = {
  webhookId: string;
  totalDeliveries: number;
  successCount: number;
  failureCount: number;
  lastDeliveryAt: number | null;
};

export type WebhookStats = WebhookStatsValue & { id: WebhookStatsId };

export type WebhooksDeliveriesResourceParams = {
  webhookId: string;
};
