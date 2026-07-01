import { AssembleInvoiceMapper } from "../mappers/AssembleInvoiceMapper.js";
import { LineItemByInvoiceMapper } from "../mappers/LineItemByInvoiceMapper.js";
import type {
  Invoice_skip_id_,
  InvoiceStored,
  LineItem_skip_id_,
  LineItemStored,
  Invoice,
  LineItem,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetInvoiceResourceInputs extends SharedCollections {
  readonly invoices: EagerCollection<Invoice_skip_id_, InvoiceStored>;
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
}

export class GetInvoiceResource implements Resource<GetInvoiceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetInvoiceResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, Invoice> {
    const lineItemsByInvoice = inputs.lineItems.map(LineItemByInvoiceMapper);
    return inputs.invoices.map(AssembleInvoiceMapper, lineItemsByInvoice);
  }
}
