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

export type CancelOrderRequest = { readonly reason: string } & {
  readonly [key: string]: Json | null;
};

export type CancelOrderRequest_skip_id_ = { readonly reason: string } & {
  readonly [key: string]: Json | null;
};

export type CancelOrderRequest_skip_value_ = { readonly reason: string } & {
  readonly [key: string]: Json | null;
};

export type CreateOrderRequest = {
  readonly items: OrderLineInput[];
  readonly shippingAddress?: string;
} & { readonly [key: string]: Json | null };

export type CreateOrderRequest_skip_id_ = {
  readonly items: OrderLineInput[];
  readonly shippingAddress?: string;
} & { readonly [key: string]: Json | null };

export type CreateOrderRequest_skip_value_ = {
  readonly items: OrderLineInput[];
  readonly shippingAddress?: string;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest = {
  readonly description?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type GetOrderParams = {
  readonly orderId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListOrderLinesParams = { readonly orderId: string } & {
  readonly [key: string]: Json | null;
};

export type ListOrdersParams = {
  readonly status?: OrderStatus;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListProductsParams = { readonly search?: string } & {
  readonly [key: string]: Json | null;
};

export type Order = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly confirmedAt?: string;
  readonly createdAt: string;
  readonly deliveredAt?: string;
  readonly id: string;
  readonly lines: OrderLine[];
  readonly shippedAt?: string;
  readonly shippingAddress?: string;
  readonly status: OrderStatus;
  readonly totalCents: number;
  readonly trackingNumber?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type OrderLine = {
  readonly lineIndex: number;
  readonly orderId: string;
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
} & { readonly [key: string]: Json | null };

export type OrderLineByOrderValue = {
  readonly lineIndex: number;
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
} & { readonly [key: string]: Json | null };

export type OrderLineInput = {
  readonly productId: string;
  readonly quantity: number;
} & { readonly [key: string]: Json | null };

export type OrderLineInput_skip_id_ = {
  readonly productId: string;
  readonly quantity: number;
} & { readonly [key: string]: Json | null };

export type OrderLineInput_skip_value_ = {
  readonly productId: string;
  readonly quantity: number;
} & { readonly [key: string]: Json | null };

export type OrderLineKey = {
  readonly lineIndex: number;
  readonly orderId: string;
} & { readonly [key: string]: Json | null };

export type OrderLineList = { readonly items: OrderLine[] } & {
  readonly [key: string]: Json | null;
};

export type OrderLineList_skip_id_ = { readonly items: OrderLine[] } & {
  readonly [key: string]: Json | null;
};

export type OrderLineList_skip_value_ = { readonly items: OrderLine[] } & {
  readonly [key: string]: Json | null;
};

export type OrderLine_skip_id_ = {
  readonly lineIndex: number;
  readonly orderId: string;
} & { readonly [key: string]: Json | null };

export type OrderLine_skip_value_ = {
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
} & { readonly [key: string]: Json | null };

export type OrderList = { readonly items: Order[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type OrderList_skip_id_ = {
  readonly items: Order[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type OrderList_skip_value_ = {
  readonly items: Order[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type OrderStatus =
  | "PENDING"
  | "CONFIRMED"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStatus_skip_id_ =
  | "PENDING"
  | "CONFIRMED"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStatus_skip_value_ =
  | "PENDING"
  | "CONFIRMED"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStored = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly confirmedAt?: string;
  readonly createdAt: string;
  readonly deliveredAt?: string;
  readonly shippedAt?: string;
  readonly shippingAddress?: string;
  readonly status: OrderStatus;
  readonly trackingNumber?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Order_skip_id_ = string;

export type Order_skip_value_ = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly confirmedAt?: string;
  readonly createdAt: string;
  readonly deliveredAt?: string;
  readonly lines: OrderLine[];
  readonly shippedAt?: string;
  readonly shippingAddress?: string;
  readonly status: OrderStatus;
  readonly totalCents: number;
  readonly trackingNumber?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Product = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly priceCents: number;
  readonly stock: number;
} & { readonly [key: string]: Json | null };

export type ProductList = {
  readonly items: Product[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ProductList_skip_id_ = {
  readonly items: Product[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ProductList_skip_value_ = {
  readonly items: Product[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly stock: number;
} & { readonly [key: string]: Json | null };

export type ShipOrderRequest = { readonly trackingNumber: string } & {
  readonly [key: string]: Json | null;
};

export type ShipOrderRequest_skip_id_ = { readonly trackingNumber: string } & {
  readonly [key: string]: Json | null;
};

export type ShipOrderRequest_skip_value_ = {
  readonly trackingNumber: string;
} & { readonly [key: string]: Json | null };

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

export type UpdateProductRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly stock?: number;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
