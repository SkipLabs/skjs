import { AssembleInvoiceMapper } from "./mappers/AssembleInvoiceMapper.js";
import { InvoicesByCustomerMapper } from "./mappers/InvoicesByCustomerMapper.js";
import { LineItemAmountByInvoiceMapper } from "./mappers/LineItemAmountByInvoiceMapper.js";
import { LineItemsByInvoiceWithIdMapper } from "./mappers/LineItemsByInvoiceWithIdMapper.js";
import { PaymentAmountByInvoiceMapper } from "./mappers/PaymentAmountByInvoiceMapper.js";
import { PaymentsByInvoiceWithIdMapper } from "./mappers/PaymentsByInvoiceWithIdMapper.js";
import { SumNumberReducer } from "./reducers/SumNumberReducer.js";
import type {
  Customer_skip_id_,
  Customer,
  CustomerStored,
  Invoice_skip_id_,
  Invoice,
  InvoiceStored,
  LineItemKey,
  LineItemStored,
  PaymentKey,
  PaymentStored,
  User_skip_id_,
  User,
  User_skip_value_,
  Invoice_skip_value_,
  LineItem,
  Payment,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly customers: EagerCollection<Customer_skip_id_, CustomerStored>;
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: EagerCollection<LineItemKey, LineItemStored>;
  readonly payments: EagerCollection<PaymentKey, PaymentStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, CustomerStored>;
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
  readonly invoicesAssembled: EagerCollection<
    Invoice_skip_id_,
    Invoice_skip_value_
  >;
  readonly invoicesByCustomer: EagerCollection<
    Customer_skip_id_,
    InvoiceStored
  >;
  readonly lineItems: EagerCollection<LineItemKey, LineItemStored>;
  readonly lineItemsByInvoice: EagerCollection<Invoice_skip_id_, LineItem>;
  readonly payments: EagerCollection<PaymentKey, PaymentStored>;
  readonly paymentsByInvoice: EagerCollection<Invoice_skip_id_, Payment>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const paymentAmountByInvoice = inputs.payments.map(
    PaymentAmountByInvoiceMapper,
  );
  const amountPaidByInvoice = paymentAmountByInvoice.reduce(SumNumberReducer);
  const lineItemsByInvoice = inputs.lineItems.map(
    LineItemsByInvoiceWithIdMapper,
  );
  const lineItemAmountByInvoice = inputs.lineItems.map(
    LineItemAmountByInvoiceMapper,
  );
  const totalAmountByInvoice = lineItemAmountByInvoice.reduce(SumNumberReducer);
  const invoicesAssembled = inputs.invoices.map(
    AssembleInvoiceMapper,
    lineItemsByInvoice,
    totalAmountByInvoice,
    amountPaidByInvoice,
  );
  const invoicesByCustomer = inputs.invoices.map(InvoicesByCustomerMapper);
  const output_customers = inputs.customers;
  const output_invoices = inputs.invoices;
  const output_invoicesAssembled = invoicesAssembled;
  const output_invoicesByCustomer = invoicesByCustomer;
  const output_lineItems = inputs.lineItems;
  const output_lineItemsByInvoice = lineItemsByInvoice;
  const output_payments = inputs.payments;
  const paymentsByInvoice = inputs.payments.map(PaymentsByInvoiceWithIdMapper);
  const output_paymentsByInvoice = paymentsByInvoice;
  const output_users = inputs.users;
  return {
    customers: output_customers,
    invoices: output_invoices,
    invoicesAssembled: output_invoicesAssembled,
    invoicesByCustomer: output_invoicesByCustomer,
    lineItems: output_lineItems,
    lineItemsByInvoice: output_lineItemsByInvoice,
    payments: output_payments,
    paymentsByInvoice: output_paymentsByInvoice,
    users: output_users,
  };
}
