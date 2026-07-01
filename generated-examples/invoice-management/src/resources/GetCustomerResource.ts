import { AssembleCustomerMapper } from "../mappers/AssembleCustomerMapper.js";
import type {
  Customer_skip_id_,
  CustomerStored,
  Customer_skip_value_,
  Customer,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetCustomerResourceInputs extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, CustomerStored>;
}

export class GetCustomerResource implements Resource<GetCustomerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCustomerResourceInputs,
    _context: Context,
  ): EagerCollection<Customer_skip_id_, Customer_skip_value_> {
    return inputs.customers.map(AssembleCustomerMapper);
  }
}
