import type { Customer_skip_id_, InvoiceStored, Customer } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface InvoicesByCustomerResourceInputs extends SharedCollections {
  readonly invoicesByCustomer: EagerCollection<
    Customer_skip_id_,
    InvoiceStored
  >;
}

export class InvoicesByCustomerResource implements Resource<InvoicesByCustomerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: InvoicesByCustomerResourceInputs,
    _context: Context,
  ): EagerCollection<Customer_skip_id_, InvoiceStored> {
    return inputs.invoicesByCustomer;
  }
}
