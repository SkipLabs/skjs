import { OrderByOwnerMapper } from "../mappers/OrderByOwnerMapper.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
  User_skip_id_,
  Order,
  ListOrdersParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListOrdersResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
}

export class ListOrdersResource implements Resource<ListOrdersResourceInputs> {
  private readonly userId: string;

  constructor(params: ListOrdersParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListOrdersResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Order> {
    return inputs.orders.map(OrderByOwnerMapper, this.userId);
  }
}
