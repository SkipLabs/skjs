export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Availability = {
  readonly asOf: string;
  readonly available: number;
  readonly onHand: number;
  readonly reserved: number;
  readonly skuId: string;
};

export type Availability_skip_id_ = {
  readonly asOf: string;
  readonly available: number;
  readonly onHand: number;
  readonly reserved: number;
  readonly skuId: string;
};

export type Availability_skip_value_ = {
  readonly asOf: string;
  readonly available: number;
  readonly onHand: number;
  readonly reserved: number;
  readonly skuId: string;
};

export type CreateOrderRequest = {
  readonly customerReference?: string;
  readonly quantity: number;
  readonly skuId: string;
};

export type CreateOrderRequest_skip_id_ = {
  readonly customerReference?: string;
  readonly quantity: number;
  readonly skuId: string;
};

export type CreateOrderRequest_skip_value_ = {
  readonly customerReference?: string;
  readonly quantity: number;
  readonly skuId: string;
};

export type CreateReceiptRequest = {
  readonly quantity: number;
  readonly reference?: string;
  readonly skuId: string;
};

export type CreateReceiptRequest_skip_id_ = {
  readonly quantity: number;
  readonly reference?: string;
  readonly skuId: string;
};

export type CreateReceiptRequest_skip_value_ = {
  readonly quantity: number;
  readonly reference?: string;
  readonly skuId: string;
};

export type CreateSkuRequest = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly unit: string;
};

export type CreateSkuRequest_skip_id_ = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly unit: string;
};

export type CreateSkuRequest_skip_value_ = {
  readonly code: string;
  readonly description?: string;
  readonly name: string;
  readonly unit: string;
};

export type GetMeParams = { readonly userId: string };

export type GetOrderParams = { readonly orderId: string };

export type GetReceiptParams = { readonly receiptId: string };

export type GetSkuAvailabilityParams = { readonly skuId: string };

export type GetSkuParams = { readonly skuId: string };

export type ListOrdersParams = {
  readonly skuId?: string;
  readonly status?: string;
};

export type ListReceiptsParams = { readonly skuId?: string };

export type ListSkusParams = { readonly search?: string };

export type Order = {
  readonly allocatedAt?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly customerReference?: string;
  readonly fulfilledAt?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly skuId: string;
  readonly status: OrderStatus;
};

export type OrderList = { readonly items: Order[]; readonly total: number };

export type OrderList_skip_id_ = {
  readonly items: Order[];
  readonly total: number;
};

export type OrderList_skip_value_ = {
  readonly items: Order[];
  readonly total: number;
};

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
  readonly customerReference?: string;
  readonly fulfilledAt?: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly skuId: string;
  readonly status: OrderStatus;
};

export type QuantityAccum = number;

export type Receipt = {
  readonly id: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly receivedAt: string;
  readonly reference?: string;
  readonly skuId: string;
};

export type ReceiptList = { readonly items: Receipt[]; readonly total: number };

export type ReceiptList_skip_id_ = {
  readonly items: Receipt[];
  readonly total: number;
};

export type ReceiptList_skip_value_ = {
  readonly items: Receipt[];
  readonly total: number;
};

export type Receipt_skip_id_ = string;

export type Receipt_skip_value_ = {
  readonly ownerId: string;
  readonly quantity: number;
  readonly receivedAt: string;
  readonly reference?: string;
  readonly skuId: string;
};

export type Sku = {
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly unit: string;
};

export type SkuIdKey = string;

export type SkuList = { readonly items: Sku[]; readonly total: number };

export type SkuList_skip_id_ = {
  readonly items: Sku[];
  readonly total: number;
};

export type SkuList_skip_value_ = {
  readonly items: Sku[];
  readonly total: number;
};

export type Sku_skip_id_ = string;

export type Sku_skip_value_ = {
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly unit: string;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateSkuRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
};

export type UpdateSkuRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
};

export type UpdateSkuRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly unit?: string;
};

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};
