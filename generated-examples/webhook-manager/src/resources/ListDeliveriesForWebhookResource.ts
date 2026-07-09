import { FilterDeliveryByWebhookAndStatusMapper } from "../mappers/FilterDeliveryByWebhookAndStatusMapper.js";
import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  ListDeliveriesForWebhookParams,
  Delivery,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListDeliveriesForWebhookResourceInputs extends SharedCollections {
  readonly deliveries: EagerCollection<Delivery_skip_id_, Delivery_skip_value_>;
}

export class ListDeliveriesForWebhookResource implements Resource<ListDeliveriesForWebhookResourceInputs> {
  private readonly status: string | null;
  private readonly webhookId: string;

  constructor(params: ListDeliveriesForWebhookParams) {
    this.status = params.status ?? null;
    this.webhookId = params.webhookId;
  }

  instantiate(
    inputs: ListDeliveriesForWebhookResourceInputs,
    _context: Context,
  ): EagerCollection<Delivery_skip_id_, Delivery_skip_value_> {
    return inputs.deliveries.map(
      FilterDeliveryByWebhookAndStatusMapper,
      this.webhookId,
      this.status,
    );
  }
}
