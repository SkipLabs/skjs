export type DraftSentPaidOverdueEnum = "draft" | "sent" | "paid" | "overdue";

export type InvoiceId = string;

export type InvoiceValue = {
  customerId: string;
  status: DraftSentPaidOverdueEnum;
  createdAt: number;
  dueDate: number;
  totalAmount: number;
};

export type Invoice = InvoiceValue & { id: InvoiceId };

export type LineItemId = string;

export type LineItemValue = {
  invoiceId: string;
  description: string;
  quantity: number;
  unitPrice: number;
  amount: number;
};

export type LineItem = LineItemValue & { id: LineItemId };

export type CustomerId = string;

export type CustomerValue = {
  name: string;
  email: string;
};

export type Customer = CustomerValue & { id: CustomerId };

export type InvoicesLineItemsResourceParams = {
  invoiceId: string;
};

export type CustomersInvoicesResourceParams = {
  customerId: string;
};
