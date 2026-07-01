import type { Invoice_skip_id_, Payment, Invoice } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListPaymentsResourceInputs extends SharedCollections {
  readonly paymentsByInvoice: EagerCollection<Invoice_skip_id_, Payment>;
}

export class ListPaymentsResource implements Resource<ListPaymentsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListPaymentsResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, Payment> {
    return inputs.paymentsByInvoice;
  }
}
