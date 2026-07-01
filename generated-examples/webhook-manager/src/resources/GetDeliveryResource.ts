import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  Delivery,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetDeliveryResourceInputs extends SharedCollections {
  readonly deliveries: EagerCollection<Delivery_skip_id_, Delivery_skip_value_>;
}

export class GetDeliveryResource implements Resource<GetDeliveryResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetDeliveryResourceInputs,
    _context: Context,
  ): EagerCollection<Delivery_skip_id_, Delivery_skip_value_> {
    return inputs.deliveries;
  }
}
