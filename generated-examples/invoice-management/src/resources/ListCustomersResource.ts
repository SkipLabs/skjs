import type {
  Customer_skip_id_,
  Customer_skip_value_,
  Customer,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCustomersResourceInputs extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, Customer_skip_value_>;
}

export class ListCustomersResource implements Resource<ListCustomersResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListCustomersResourceInputs,
    _context: Context,
  ): EagerCollection<Customer_skip_id_, Customer_skip_value_> {
    return inputs.customers;
  }
}
