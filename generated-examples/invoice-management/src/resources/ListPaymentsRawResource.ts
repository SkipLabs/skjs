import type { PaymentKey, PaymentStored } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListPaymentsRawResourceInputs extends SharedCollections {
  readonly payments: EagerCollection<PaymentKey, PaymentStored>;
}

export class ListPaymentsRawResource implements Resource<ListPaymentsRawResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListPaymentsRawResourceInputs,
    _context: Context,
  ): EagerCollection<PaymentKey, PaymentStored> {
    return inputs.payments;
  }
}
