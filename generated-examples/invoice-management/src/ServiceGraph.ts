import type {
  Customer_skip_id_,
  Customer,
  Customer_skip_value_,
  Invoice_skip_id_,
  Invoice,
  InvoiceStored,
  LineItem_skip_id_,
  LineItem,
  LineItemStored,
  User_skip_id_,
  User,
  UserStored,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly customers: EagerCollection<Customer_skip_id_, Customer_skip_value_>;
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
  readonly users: EagerCollection<User_skip_id_, UserStored>;
}

export interface GraphCollections extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, Customer_skip_value_>;
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
  readonly users: EagerCollection<User_skip_id_, UserStored>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_customers = inputs.customers;
  const output_invoices = inputs.invoices;
  const output_lineItems = inputs.lineItems;
  const output_users = inputs.users;
  return {
    customers: output_customers,
    invoices: output_invoices,
    lineItems: output_lineItems,
    users: output_users,
  };
}
