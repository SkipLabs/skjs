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

export type CreateCustomerRequest = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type CreateCustomerRequest_skip_id_ = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type CreateCustomerRequest_skip_value_ = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type CreateInvoiceRequest = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly lineItems: CreateLineItemInline[];
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type CreateInvoiceRequest_skip_id_ = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly lineItems: CreateLineItemInline[];
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type CreateInvoiceRequest_skip_value_ = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly lineItems: CreateLineItemInline[];
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type CreateLineItemInline = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreateLineItemInline_skip_id_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreateLineItemInline_skip_value_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreateLineItemRequest = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreateLineItemRequest_skip_id_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreateLineItemRequest_skip_value_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type CreatePaymentRequest = {
  readonly amount: number;
  readonly method?: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type CreatePaymentRequest_skip_id_ = {
  readonly amount: number;
  readonly method?: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type CreatePaymentRequest_skip_value_ = {
  readonly amount: number;
  readonly method?: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type Customer = {
  readonly billingAddress?: string;
  readonly createdAt: string;
  readonly email?: string;
  readonly id: string;
  readonly name: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly phone?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type CustomerList = {
  readonly items: Customer[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type CustomerList_skip_id_ = {
  readonly items: Customer[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type CustomerList_skip_value_ = {
  readonly items: Customer[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type CustomerStored = {
  readonly billingAddress?: string;
  readonly createdAt: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly phone?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Customer_skip_id_ = string;

export type Customer_skip_value_ = {
  readonly billingAddress?: string;
  readonly createdAt: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly phone?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type GetCustomerParams = { readonly customerId: string } & {
  readonly [key: string]: Json | null;
};

export type GetInvoiceParams = { readonly invoiceId: string } & {
  readonly [key: string]: Json | null;
};

export type Invoice = {
  readonly amountPaid: number;
  readonly balanceDue: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly id: string;
  readonly invoiceNumber: string;
  readonly issuedAt?: string;
  readonly lineItems: LineItem[];
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly status: InvoiceStatus;
  readonly totalAmount: number;
  readonly voidedAt?: string;
} & { readonly [key: string]: Json | null };

export type InvoiceAmount = number;

export type InvoiceList = {
  readonly items: Invoice[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type InvoiceList_skip_id_ = {
  readonly items: Invoice[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type InvoiceList_skip_value_ = {
  readonly items: Invoice[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type InvoiceStatus =
  | "DRAFT"
  | "ISSUED"
  | "PARTIALLY_PAID"
  | "PAID"
  | "VOID";

export type InvoiceStatus_skip_id_ =
  | "DRAFT"
  | "ISSUED"
  | "PARTIALLY_PAID"
  | "PAID"
  | "VOID";

export type InvoiceStatus_skip_value_ =
  | "DRAFT"
  | "ISSUED"
  | "PARTIALLY_PAID"
  | "PAID"
  | "VOID";

export type InvoiceStored = {
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly issuedAt?: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly status: InvoiceStatus;
  readonly voidedAt?: string;
} & { readonly [key: string]: Json | null };

export type Invoice_skip_id_ = string;

export type Invoice_skip_value_ = {
  readonly amountPaid: number;
  readonly balanceDue: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly issuedAt?: string;
  readonly lineItems: LineItem[];
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly status: InvoiceStatus;
  readonly totalAmount: number;
  readonly voidedAt?: string;
} & { readonly [key: string]: Json | null };

export type LineItem = {
  readonly description: string;
  readonly id: string;
  readonly invoiceId: string;
  readonly lineTotal: number;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type LineItemKey = {
  readonly id: string;
  readonly invoiceId: string;
} & { readonly [key: string]: Json | null };

export type LineItemList = { readonly items: LineItem[] } & {
  readonly [key: string]: Json | null;
};

export type LineItemList_skip_id_ = { readonly items: LineItem[] } & {
  readonly [key: string]: Json | null;
};

export type LineItemList_skip_value_ = { readonly items: LineItem[] } & {
  readonly [key: string]: Json | null;
};

export type LineItemStored = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type LineItem_skip_id_ = {
  readonly id: string;
  readonly invoiceId: string;
} & { readonly [key: string]: Json | null };

export type LineItem_skip_value_ = {
  readonly description: string;
  readonly lineTotal: number;
  readonly quantity: number;
  readonly unitPrice: number;
} & { readonly [key: string]: Json | null };

export type ListCustomersParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListLineItemsParams = { readonly invoiceId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPaymentsParams = { readonly invoiceId: string } & {
  readonly [key: string]: Json | null;
};

export type Payment = {
  readonly amount: number;
  readonly id: string;
  readonly invoiceId: string;
  readonly method?: string;
  readonly paidAt: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type PaymentKey = { readonly id: string; readonly invoiceId: string } & {
  readonly [key: string]: Json | null;
};

export type PaymentList = { readonly items: Payment[] } & {
  readonly [key: string]: Json | null;
};

export type PaymentList_skip_id_ = { readonly items: Payment[] } & {
  readonly [key: string]: Json | null;
};

export type PaymentList_skip_value_ = { readonly items: Payment[] } & {
  readonly [key: string]: Json | null;
};

export type PaymentStored = {
  readonly amount: number;
  readonly method?: string;
  readonly paidAt: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type Payment_skip_id_ = {
  readonly id: string;
  readonly invoiceId: string;
} & { readonly [key: string]: Json | null };

export type Payment_skip_value_ = {
  readonly amount: number;
  readonly method?: string;
  readonly paidAt: string;
  readonly reference?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCustomerRequest = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCustomerRequest_skip_id_ = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCustomerRequest_skip_value_ = {
  readonly billingAddress?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
} & { readonly [key: string]: Json | null };

export type UpdateInvoiceRequest = {
  readonly dueDate?: string;
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type UpdateInvoiceRequest_skip_id_ = {
  readonly dueDate?: string;
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type UpdateInvoiceRequest_skip_value_ = {
  readonly dueDate?: string;
  readonly notes?: string;
} & { readonly [key: string]: Json | null };

export type UpdateLineItemRequest = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
} & { readonly [key: string]: Json | null };

export type UpdateLineItemRequest_skip_id_ = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
} & { readonly [key: string]: Json | null };

export type UpdateLineItemRequest_skip_value_ = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly companyName?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly companyName?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
