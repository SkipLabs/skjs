export type PendingConfirmedmpnxwyEnum = "cancelled" | "confirmed" | "delivered" | "pending" | "shipped";


export type CustomerId = string;

export type CustomerValue = {
  name: string;
  email: string;
  address: string | null;
};

export type Customer = CustomerValue & { id: CustomerId };

export type ProductId = string;

export type ProductValue = {
  name: string;
  description: string | null;
  price: number;
  stock: number;
};

export type Product = ProductValue & { id: ProductId };

export type OrderId = string;

export type OrderValue = {
  customerId: string;
  itemCount: number;
  totalAmount: number;
  status: PendingConfirmedmpnxwyEnum;
  createdAt: number;
  updatedAt: number | null;
};

export type Order = OrderValue & { id: OrderId };

export type OrderSummaryId = string;

export type OrderSummaryValue = {
  customerId: string;
  customerName: string;
  itemCount: number;
  totalAmount: number;
  status: string;
  createdAt: number;
};

export type OrderSummary = OrderSummaryValue & { id: OrderSummaryId };
