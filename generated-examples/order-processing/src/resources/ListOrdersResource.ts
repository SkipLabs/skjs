import { FilterOrdersByCustomerMapper } from "../mappers/FilterOrdersByCustomerMapper.js";
import type {
  Order_skip_id_,
  OrderStored,
  ListOrdersParams,
  Order,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListOrdersResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
}

export class ListOrdersResource implements Resource<ListOrdersResourceInputs> {
  private readonly userId: string;

  constructor(params: ListOrdersParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListOrdersResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderStored> {
    return inputs.orders.map(FilterOrdersByCustomerMapper, this.userId);
  }
}
