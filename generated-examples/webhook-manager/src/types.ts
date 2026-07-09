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

export type CreateDeliveryRequest = {
  readonly attemptCount: number;
  readonly errorMessage?: string;
  readonly eventType: string;
  readonly payload: string;
  readonly responseBody?: string;
  readonly responseStatusCode?: number;
  readonly status: DeliveryStatus;
} & { readonly [key: string]: Json | null };

export type CreateDeliveryRequest_skip_id_ = {
  readonly attemptCount: number;
  readonly errorMessage?: string;
  readonly eventType: string;
  readonly payload: string;
  readonly responseBody?: string;
  readonly responseStatusCode?: number;
  readonly status: DeliveryStatus;
} & { readonly [key: string]: Json | null };

export type CreateDeliveryRequest_skip_value_ = {
  readonly attemptCount: number;
  readonly errorMessage?: string;
  readonly eventType: string;
  readonly payload: string;
  readonly responseBody?: string;
  readonly responseStatusCode?: number;
  readonly status: DeliveryStatus;
} & { readonly [key: string]: Json | null };

export type CreateSubscriptionRequest = { readonly eventType: string } & {
  readonly [key: string]: Json | null;
};

export type CreateSubscriptionRequest_skip_id_ = {
  readonly eventType: string;
} & { readonly [key: string]: Json | null };

export type CreateSubscriptionRequest_skip_value_ = {
  readonly eventType: string;
} & { readonly [key: string]: Json | null };

export type CreateWebhookRequest = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };

export type CreateWebhookRequest_skip_id_ = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };

export type CreateWebhookRequest_skip_value_ = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };

export type Delivery = {
  readonly attemptCount: number;
  readonly attemptedAt: string;
  readonly errorMessage?: string;
  readonly eventType: string;
  readonly id: string;
  readonly payload: string;
  readonly responseBody?: string;
  readonly responseStatusCode?: number;
  readonly status: DeliveryStatus;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type DeliveryList = {
  readonly items: Delivery[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type DeliveryList_skip_id_ = {
  readonly items: Delivery[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type DeliveryList_skip_value_ = {
  readonly items: Delivery[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type DeliverySortKey = {
  readonly attemptedAt: number;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type DeliveryStatus = "pending" | "success" | "failed";

export type DeliveryStatus_skip_id_ = "pending" | "success" | "failed";

export type DeliveryStatus_skip_value_ = "pending" | "success" | "failed";

export type Delivery_skip_id_ = string;

export type Delivery_skip_value_ = {
  readonly attemptCount: number;
  readonly attemptedAt: string;
  readonly errorMessage?: string;
  readonly eventType: string;
  readonly payload: string;
  readonly responseBody?: string;
  readonly responseStatusCode?: number;
  readonly status: DeliveryStatus;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type EventType = {
  readonly description?: string;
  readonly key: string;
} & { readonly [key: string]: Json | null };

export type EventTypeList = { readonly items: EventType[] } & {
  readonly [key: string]: Json | null;
};

export type EventTypeList_skip_id_ = { readonly items: EventType[] } & {
  readonly [key: string]: Json | null;
};

export type EventTypeList_skip_value_ = { readonly items: EventType[] } & {
  readonly [key: string]: Json | null;
};

export type EventType_skip_id_ = string;

export type EventType_skip_value_ = { readonly description?: string } & {
  readonly [key: string]: Json | null;
};

export type GetDeliveryParams = {
  readonly deliveryId: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type GetSubscriptionParams = {
  readonly eventType: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type GetWebhookParams = {
  readonly userId: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type ListDeliveriesForWebhookParams = {
  readonly status?: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type ListSubscriptionsForWebhookParams = {
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type ListWebhooksParams = {
  readonly active?: boolean;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Subscription = {
  readonly createdAt: string;
  readonly eventType: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type SubscriptionList = { readonly items: Subscription[] } & {
  readonly [key: string]: Json | null;
};

export type SubscriptionList_skip_id_ = { readonly items: Subscription[] } & {
  readonly [key: string]: Json | null;
};

export type SubscriptionList_skip_value_ = {
  readonly items: Subscription[];
} & { readonly [key: string]: Json | null };

export type Subscription_skip_id_ = {
  readonly eventType: string;
  readonly webhookId: string;
} & { readonly [key: string]: Json | null };

export type Subscription_skip_value_ = { readonly createdAt: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWebhookRequest = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret?: string;
  readonly url?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWebhookRequest_skip_id_ = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret?: string;
  readonly url?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWebhookRequest_skip_value_ = {
  readonly active?: boolean;
  readonly description?: string;
  readonly secret?: string;
  readonly url?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type Webhook = {
  readonly active: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };

export type WebhookList = {
  readonly items: Webhook[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type WebhookList_skip_id_ = {
  readonly items: Webhook[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type WebhookList_skip_value_ = {
  readonly items: Webhook[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type WebhookStored = {
  readonly active: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly ownerId: string;
  readonly secret: string;
  readonly updatedAt: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };

export type Webhook_skip_id_ = string;

export type Webhook_skip_value_ = {
  readonly active: boolean;
  readonly createdAt: string;
  readonly description?: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly url: string;
} & { readonly [key: string]: Json | null };
