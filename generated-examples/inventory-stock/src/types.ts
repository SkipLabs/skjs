import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code?: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CreateOrderRequest = {
  readonly customerRef?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateOrderRequest_skip_id_ = {
  readonly customerRef?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateOrderRequest_skip_value_ = {
  readonly customerRef?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateReceiptRequest = {
  readonly note?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateReceiptRequest_skip_id_ = {
  readonly note?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateReceiptRequest_skip_value_ = {
  readonly note?: string;
  readonly quantity: number;
  readonly skuId: string;
} & { readonly [key: string]: Json | null };

export type CreateSkuRequest = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type CreateSkuRequest_skip_id_ = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type CreateSkuRequest_skip_value_ = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type GetOrderParams = { readonly orderId: string } & {
  readonly [key: string]: Json | null;
};

export type GetReceiptParams = { readonly receiptId: string } & {
  readonly [key: string]: Json | null;
};

export type GetSkuAvailabilityParams = { readonly skuId: string } & {
  readonly [key: string]: Json | null;
};

export type GetSkuParams = { readonly skuId: string } & {
  readonly [key: string]: Json | null;
};

export type ListOrdersParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListReceiptsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListSkusParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Order = {
  readonly allocatedAt?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly customerRef?: string;
  readonly fulfilledAt?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly skuId: string;
  readonly status: OrderStatus;
} & { readonly [key: string]: Json | null };

export type OrderStatus = "PENDING" | "ALLOCATED" | "FULFILLED" | "CANCELLED";

export type OrderStatus_skip_id_ =
  | "PENDING"
  | "ALLOCATED"
  | "FULFILLED"
  | "CANCELLED";

export type OrderStatus_skip_value_ =
  | "PENDING"
  | "ALLOCATED"
  | "FULFILLED"
  | "CANCELLED";

export type Order_skip_id_ = string;

export type Order_skip_value_ = {
  readonly allocatedAt?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly customerRef?: string;
  readonly fulfilledAt?: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly skuId: string;
  readonly status: OrderStatus;
} & { readonly [key: string]: Json | null };

export type Receipt = {
  readonly createdAt: string;
  readonly id: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly receivedAt?: string;
  readonly skuId: string;
  readonly status: ReceiptStatus;
} & { readonly [key: string]: Json | null };

export type ReceiptStatus = "PENDING" | "RECEIVED";

export type ReceiptStatus_skip_id_ = "PENDING" | "RECEIVED";

export type ReceiptStatus_skip_value_ = "PENDING" | "RECEIVED";

export type Receipt_skip_id_ = string;

export type Receipt_skip_value_ = {
  readonly createdAt: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly receivedAt?: string;
  readonly skuId: string;
  readonly status: ReceiptStatus;
} & { readonly [key: string]: Json | null };

export type Sku = {
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type SkuAvailability = {
  readonly available: number;
  readonly belowReorderThreshold: boolean;
  readonly skuId: string;
  readonly totalAllocated: number;
  readonly totalOnHand: number;
  readonly totalReceived: number;
  readonly totalReserved: number;
} & { readonly [key: string]: Json | null };

export type SkuAvailabilityAccum = {
  readonly totalAllocated: number;
  readonly totalReceived: number;
  readonly totalReserved: number;
} & { readonly [key: string]: Json | null };

export type SkuAvailability_skip_id_ = {
  readonly available: number;
  readonly belowReorderThreshold: boolean;
  readonly skuId: string;
  readonly totalAllocated: number;
  readonly totalOnHand: number;
  readonly totalReceived: number;
  readonly totalReserved: number;
} & { readonly [key: string]: Json | null };

export type SkuAvailability_skip_value_ = {
  readonly available: number;
  readonly belowReorderThreshold: boolean;
  readonly skuId: string;
  readonly totalAllocated: number;
  readonly totalOnHand: number;
  readonly totalReceived: number;
  readonly totalReserved: number;
} & { readonly [key: string]: Json | null };

export type Sku_skip_id_ = string;

export type Sku_skip_value_ = {
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSkuRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSkuRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSkuRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly reorderThreshold?: number;
  readonly unit?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
