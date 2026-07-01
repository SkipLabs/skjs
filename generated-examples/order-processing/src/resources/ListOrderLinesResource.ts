import { FilterOrderLinesByOrderMapper } from "../mappers/FilterOrderLinesByOrderMapper.js";
import type {
  OrderLineKey,
  OrderLine_skip_value_,
  ListOrderLinesParams,
  OrderLine,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListOrderLinesResourceInputs extends SharedCollections {
  readonly orderLines: EagerCollection<OrderLineKey, OrderLine_skip_value_>;
}

export class ListOrderLinesResource implements Resource<ListOrderLinesResourceInputs> {
  private readonly orderId: string;

  constructor(params: ListOrderLinesParams) {
    this.orderId = params.orderId;
  }

  instantiate(
    inputs: ListOrderLinesResourceInputs,
    _context: Context,
  ): EagerCollection<OrderLineKey, OrderLine_skip_value_> {
    return inputs.orderLines.map(FilterOrderLinesByOrderMapper, this.orderId);
  }
}
