export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type CancelOrderRequest = { readonly reason: string };

export type CancelOrderRequest_skip_id_ = { readonly reason: string };

export type CancelOrderRequest_skip_value_ = { readonly reason: string };

export type CreateOrderItem = {
  readonly productId: string;
  readonly quantity: number;
};

export type CreateOrderItem_skip_id_ = {
  readonly productId: string;
  readonly quantity: number;
};

export type CreateOrderItem_skip_value_ = {
  readonly productId: string;
  readonly quantity: number;
};

export type CreateOrderRequest = { readonly items: CreateOrderItem[] };

export type CreateOrderRequest_skip_id_ = { readonly items: CreateOrderItem[] };

export type CreateOrderRequest_skip_value_ = {
  readonly items: CreateOrderItem[];
};

export type CreateProductRequest = {
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly sku?: string;
  readonly unitPriceCents: number;
};

export type CreateProductRequest_skip_id_ = {
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly sku?: string;
  readonly unitPriceCents: number;
};

export type CreateProductRequest_skip_value_ = {
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly sku?: string;
  readonly unitPriceCents: number;
};

export type GetOrderParams = { readonly orderId: string };

export type GetProductParams = { readonly productId: string };

export type ListLineItemsByOrderParams = { readonly orderId: string };

export type ListOrdersParams = { readonly userId: string };

export type ListPaymentsByOrderParams = { readonly orderId: string };

export type Order = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly deliveredAt?: string;
  readonly id: string;
  readonly items: OrderLineItem[];
  readonly paidAt?: string;
  readonly paymentMethod?: PaymentMethod;
  readonly paymentStatus: PaymentStatus;
  readonly refundedAt?: string;
  readonly shippedAt?: string;
  readonly status: OrderStatus;
  readonly totalCents: number;
  readonly trackingNumber?: string;
};

export type OrderLineItem = {
  readonly lineNumber: number;
  readonly lineTotalCents: number;
  readonly orderId: string;
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
};

export type OrderLineItemForOrder = {
  readonly lineNumber: number;
  readonly orderId: string;
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
};

export type OrderLineItemKey = {
  readonly lineNumber: number;
  readonly orderId: string;
};

export type OrderLineItemStored = {
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
};

export type OrderLineItem_skip_id_ = {
  readonly lineNumber: number;
  readonly orderId: string;
};

export type OrderLineItem_skip_value_ = {
  readonly lineTotalCents: number;
  readonly productId: string;
  readonly productName: string;
  readonly quantity: number;
  readonly unitPriceCents: number;
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

export type OrderStatus =
  | "PENDING"
  | "PAID"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStatus_skip_id_ =
  | "PENDING"
  | "PAID"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStatus_skip_value_ =
  | "PENDING"
  | "PAID"
  | "SHIPPED"
  | "DELIVERED"
  | "CANCELLED";

export type OrderStored = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly deliveredAt?: string;
  readonly paidAt?: string;
  readonly paymentMethod?: PaymentMethod;
  readonly paymentStatus: PaymentStatus;
  readonly refundedAt?: string;
  readonly shippedAt?: string;
  readonly status: OrderStatus;
  readonly totalCents: number;
  readonly trackingNumber?: string;
};

export type Order_skip_id_ = string;

export type Order_skip_value_ = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly deliveredAt?: string;
  readonly items: OrderLineItem[];
  readonly paidAt?: string;
  readonly paymentMethod?: PaymentMethod;
  readonly paymentStatus: PaymentStatus;
  readonly refundedAt?: string;
  readonly shippedAt?: string;
  readonly status: OrderStatus;
  readonly totalCents: number;
  readonly trackingNumber?: string;
};

export type PayOrderRequest = {
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type PayOrderRequest_skip_id_ = {
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type PayOrderRequest_skip_value_ = {
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type Payment = {
  readonly amountCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly id: string;
  readonly orderId: string;
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type PaymentForOrder = {
  readonly amountCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly id: string;
  readonly orderId: string;
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type PaymentList = { readonly items: Payment[]; readonly total: number };

export type PaymentList_skip_id_ = {
  readonly items: Payment[];
  readonly total: number;
};

export type PaymentList_skip_value_ = {
  readonly items: Payment[];
  readonly total: number;
};

export type PaymentMethod = "CARD" | "BANK_TRANSFER" | "WALLET";

export type PaymentMethod_skip_id_ = "CARD" | "BANK_TRANSFER" | "WALLET";

export type PaymentMethod_skip_value_ = "CARD" | "BANK_TRANSFER" | "WALLET";

export type PaymentStatus = "UNPAID" | "PAID" | "REFUNDED";

export type PaymentStatus_skip_id_ = "UNPAID" | "PAID" | "REFUNDED";

export type PaymentStatus_skip_value_ = "UNPAID" | "PAID" | "REFUNDED";

export type Payment_skip_id_ = string;

export type Payment_skip_value_ = {
  readonly amountCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly orderId: string;
  readonly paymentMethod: PaymentMethod;
  readonly paymentReference?: string;
};

export type Product = {
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly sku?: string;
  readonly unitPriceCents: number;
  readonly updatedAt?: string;
};

export type ProductList = { readonly items: Product[]; readonly total: number };

export type ProductList_skip_id_ = {
  readonly items: Product[];
  readonly total: number;
};

export type ProductList_skip_value_ = {
  readonly items: Product[];
  readonly total: number;
};

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly sku?: string;
  readonly unitPriceCents: number;
  readonly updatedAt?: string;
};

export type ShipOrderRequest = {
  readonly carrier?: string;
  readonly trackingNumber: string;
};

export type ShipOrderRequest_skip_id_ = {
  readonly carrier?: string;
  readonly trackingNumber: string;
};

export type ShipOrderRequest_skip_value_ = {
  readonly carrier?: string;
  readonly trackingNumber: string;
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

export type UpdateProductRequest = {
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly sku?: string;
  readonly unitPriceCents?: number;
};

export type UpdateProductRequest_skip_id_ = {
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly sku?: string;
  readonly unitPriceCents?: number;
};

export type UpdateProductRequest_skip_value_ = {
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly sku?: string;
  readonly unitPriceCents?: number;
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
