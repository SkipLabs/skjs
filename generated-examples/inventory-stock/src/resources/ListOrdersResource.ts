import { FilterOrderBySkuAndStatusMapper } from "../mappers/FilterOrderBySkuAndStatusMapper.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
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
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
}

export class ListOrdersResource implements Resource<ListOrdersResourceInputs> {
  private readonly skuId: string | null;
  private readonly status: string | null;

  constructor(params: ListOrdersParams) {
    this.skuId = params.skuId ?? null;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListOrdersResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, Order_skip_value_> {
    return inputs.orders.map(
      FilterOrderBySkuAndStatusMapper,
      this.skuId,
      this.status,
    );
  }
}
