import { FilterOrderByOwnerMapper } from "../mappers/FilterOrderByOwnerMapper.js";
import type {
  Order_skip_id_,
  OrderStored,
  GetOrderParams,
  Order,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetOrderResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
}

export class GetOrderResource implements Resource<GetOrderResourceInputs> {
  private readonly orderId: string;
  private readonly userId: string;

  constructor(params: GetOrderParams) {
    this.orderId = params.orderId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetOrderResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderStored> {
    return inputs.orders.map(
      FilterOrderByOwnerMapper,
      this.userId,
      this.orderId,
    );
  }
}
