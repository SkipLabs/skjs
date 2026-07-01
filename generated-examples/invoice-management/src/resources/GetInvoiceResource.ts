import type {
  Invoice_skip_id_,
  Invoice_skip_value_,
  Invoice,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetInvoiceResourceInputs extends SharedCollections {
  readonly invoicesAssembled: EagerCollection<
    Invoice_skip_id_,
    Invoice_skip_value_
  >;
}

export class GetInvoiceResource implements Resource<GetInvoiceResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetInvoiceResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, Invoice_skip_value_> {
    return inputs.invoicesAssembled;
  }
}
