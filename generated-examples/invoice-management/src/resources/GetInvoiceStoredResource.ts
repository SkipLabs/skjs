import type { Invoice_skip_id_, InvoiceStored, Invoice } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetInvoiceStoredResourceInputs extends SharedCollections {
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
}

export class GetInvoiceStoredResource implements Resource<GetInvoiceStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetInvoiceStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, InvoiceStored> {
    return inputs.invoices;
  }
}
