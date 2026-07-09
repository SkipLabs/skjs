import { FilterOrderByOwnerAndStatusMapper } from "../mappers/FilterOrderByOwnerAndStatusMapper.js";
import type {
  Order_skip_id_,
  OrderStored,
  OrderStatus,
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
  private readonly status: OrderStatus | null;
  private readonly userId: string;

  constructor(params: ListOrdersParams) {
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListOrdersResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderStored> {
    return inputs.orders.map(
      FilterOrderByOwnerAndStatusMapper,
      this.userId,
      this.status,
    );
  }
}
