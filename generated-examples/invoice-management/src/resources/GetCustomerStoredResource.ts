import type { Customer_skip_id_, CustomerStored, Customer } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetCustomerStoredResourceInputs extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, CustomerStored>;
}

export class GetCustomerStoredResource implements Resource<GetCustomerStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCustomerStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Customer_skip_id_, CustomerStored> {
    return inputs.customers;
  }
}
