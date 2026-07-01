import type { Order_skip_id_, OrderStored, Order } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetOrderStoredResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
}

export class GetOrderStoredResource implements Resource<GetOrderStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetOrderStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderStored> {
    return inputs.orders;
  }
}
