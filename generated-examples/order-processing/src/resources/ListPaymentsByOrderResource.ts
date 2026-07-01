import type { Order_skip_id_, PaymentForOrder, Order } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPaymentsByOrderResourceInputs extends SharedCollections {
  readonly paymentsByOrder: EagerCollection<Order_skip_id_, PaymentForOrder>;
}

export class ListPaymentsByOrderResource implements Resource<ListPaymentsByOrderResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListPaymentsByOrderResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, PaymentForOrder> {
    return inputs.paymentsByOrder;
  }
}
