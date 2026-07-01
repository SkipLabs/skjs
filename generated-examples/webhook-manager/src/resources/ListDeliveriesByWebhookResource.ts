import { DeliveryByWebhookMapper } from "../mappers/DeliveryByWebhookMapper.js";
import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  Webhook_skip_id_,
  Delivery,
  Webhook,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListDeliveriesByWebhookResourceInputs extends SharedCollections {
  readonly deliveries: EagerCollection<Delivery_skip_id_, Delivery_skip_value_>;
}

export class ListDeliveriesByWebhookResource implements Resource<ListDeliveriesByWebhookResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListDeliveriesByWebhookResourceInputs,
    _context: Context,
  ): EagerCollection<Webhook_skip_id_, Delivery> {
    const deliveriesByWebhook = inputs.deliveries.map(DeliveryByWebhookMapper);
    return deliveriesByWebhook;
  }
}
