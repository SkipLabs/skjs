import { AssembleCustomerMapper } from "../mappers/AssembleCustomerMapper.js";
import { FilterCustomerByOwnerMapper } from "../mappers/FilterCustomerByOwnerMapper.js";
import type {
  Customer_skip_id_,
  CustomerStored,
  Customer_skip_value_,
  ListCustomersParams,
  Customer,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCustomersResourceInputs extends SharedCollections {
  readonly customers: EagerCollection<Customer_skip_id_, CustomerStored>;
}

export class ListCustomersResource implements Resource<ListCustomersResourceInputs> {
  private readonly userId: string;

  constructor(params: ListCustomersParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListCustomersResourceInputs,
    _context: Context,
  ): EagerCollection<Customer_skip_id_, Customer_skip_value_> {
    const filtered = inputs.customers.map(
      FilterCustomerByOwnerMapper,
      this.userId,
    );
    return filtered.map(AssembleCustomerMapper);
  }
}
