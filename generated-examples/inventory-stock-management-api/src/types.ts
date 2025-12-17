export type ProductId = string;

export type ProductValue = {
  name: string;
  initialStock: number;
};

export type Product = ProductValue & { id: ProductId };

export type OrderId = string;

export type OrderValue = {
  productId: string;
  quantity: number;
  timestamp: number;
};

export type Order = OrderValue & { id: OrderId };

export type ReceiptId = string;

export type ReceiptValue = {
  productId: string;
  quantity: number;
  timestamp: number;
};

export type Receipt = ReceiptValue & { id: ReceiptId };

export type AvailabilityId = string;

export type AvailabilityValue = {
  productId: string;
  productName: string;
  initialStock: number;
  totalOrdered: number;
  totalReceived: number;
  currentStock: number;
};

export type Availability = AvailabilityValue & { id: AvailabilityId };
