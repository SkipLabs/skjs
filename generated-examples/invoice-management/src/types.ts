export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateCustomerRequest = {
  readonly address?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type CreateCustomerRequest_skip_id_ = {
  readonly address?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type CreateCustomerRequest_skip_value_ = {
  readonly address?: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type CreateInvoiceRequest = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly notes?: string;
};

export type CreateInvoiceRequest_skip_id_ = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly notes?: string;
};

export type CreateInvoiceRequest_skip_value_ = {
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly notes?: string;
};

export type CreateLineItemRequest = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type CreateLineItemRequest_skip_id_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type CreateLineItemRequest_skip_value_ = {
  readonly description: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type Customer = {
  readonly address?: string;
  readonly createdAt: string;
  readonly email?: string;
  readonly id: string;
  readonly name: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly phone?: string;
};

export type CustomerList = { readonly customers: Customer[] };

export type CustomerList_skip_id_ = { readonly customers: Customer[] };

export type CustomerList_skip_value_ = { readonly customers: Customer[] };

export type Customer_skip_id_ = string;

export type Customer_skip_value_ = {
  readonly address?: string;
  readonly createdAt: string;
  readonly email?: string;
  readonly name: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly phone?: string;
};

export type GetCustomerParams = {
  readonly customerId: string;
  readonly userId: string;
};

export type GetInvoiceParams = {
  readonly invoiceId: string;
  readonly userId: string;
};

export type GetLineItemParams = {
  readonly invoiceId: string;
  readonly lineItemId: string;
  readonly userId: string;
};

export type Invoice = {
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly id: string;
  readonly invoiceNumber: string;
  readonly lineItems: LineItem[];
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly sentAt?: string;
  readonly status: InvoiceStatus;
  readonly subtotal: number;
  readonly total: number;
  readonly voidedAt?: string;
};

export type InvoiceList = { readonly invoices: Invoice[] };

export type InvoiceList_skip_id_ = { readonly invoices: Invoice[] };

export type InvoiceList_skip_value_ = { readonly invoices: Invoice[] };

export type InvoiceStatus = "DRAFT" | "SENT" | "PAID" | "VOID";

export type InvoiceStatus_skip_id_ = "DRAFT" | "SENT" | "PAID" | "VOID";

export type InvoiceStatus_skip_value_ = "DRAFT" | "SENT" | "PAID" | "VOID";

export type InvoiceStored = {
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly sentAt?: string;
  readonly status: InvoiceStatus;
  readonly voidedAt?: string;
};

export type Invoice_skip_id_ = string;

export type Invoice_skip_value_ = {
  readonly createdAt: string;
  readonly currency: string;
  readonly customerId: string;
  readonly dueDate?: string;
  readonly invoiceNumber: string;
  readonly lineItems: LineItem[];
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt?: string;
  readonly sentAt?: string;
  readonly status: InvoiceStatus;
  readonly subtotal: number;
  readonly total: number;
  readonly voidedAt?: string;
};

export type LineItem = {
  readonly createdAt: string;
  readonly description: string;
  readonly id: string;
  readonly invoiceId: string;
  readonly lineTotal: number;
  readonly ownerId: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type LineItemList = { readonly lineItems: LineItem[] };

export type LineItemList_skip_id_ = { readonly lineItems: LineItem[] };

export type LineItemList_skip_value_ = { readonly lineItems: LineItem[] };

export type LineItemStored = {
  readonly createdAt: string;
  readonly description: string;
  readonly invoiceId: string;
  readonly ownerId: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type LineItem_skip_id_ = string;

export type LineItem_skip_value_ = {
  readonly createdAt: string;
  readonly description: string;
  readonly invoiceId: string;
  readonly lineTotal: number;
  readonly ownerId: string;
  readonly quantity: number;
  readonly unitPrice: number;
};

export type ListCustomersParams = { readonly userId: string };

export type ListInvoicesParams = { readonly userId: string };

export type ListLineItemsParams = {
  readonly invoiceId: string;
  readonly userId: string;
};

export type UpdateCustomerRequest = {
  readonly address?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type UpdateCustomerRequest_skip_id_ = {
  readonly address?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type UpdateCustomerRequest_skip_value_ = {
  readonly address?: string;
  readonly email?: string;
  readonly name?: string;
  readonly notes?: string;
  readonly phone?: string;
};

export type UpdateInvoiceRequest = {
  readonly currency?: string;
  readonly dueDate?: string;
  readonly invoiceNumber?: string;
  readonly notes?: string;
};

export type UpdateInvoiceRequest_skip_id_ = {
  readonly currency?: string;
  readonly dueDate?: string;
  readonly invoiceNumber?: string;
  readonly notes?: string;
};

export type UpdateInvoiceRequest_skip_value_ = {
  readonly currency?: string;
  readonly dueDate?: string;
  readonly invoiceNumber?: string;
  readonly notes?: string;
};

export type UpdateLineItemRequest = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
};

export type UpdateLineItemRequest_skip_id_ = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
};

export type UpdateLineItemRequest_skip_value_ = {
  readonly description?: string;
  readonly quantity?: number;
  readonly unitPrice?: number;
};

export type UpdateMeRequest = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type User = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type UserStored = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly companyAddress?: string;
  readonly companyName?: string;
  readonly displayName?: string;
  readonly email?: string;
};
