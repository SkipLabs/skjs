import type {
  Payment_skip_id_,
  Payment_skip_value_,
  Payment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetPaymentResourceInputs extends SharedCollections {
  readonly payments: EagerCollection<Payment_skip_id_, Payment_skip_value_>;
}

export class GetPaymentResource implements Resource<GetPaymentResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetPaymentResourceInputs,
    _context: Context,
  ): EagerCollection<Payment_skip_id_, Payment_skip_value_> {
    return inputs.payments;
  }
}
