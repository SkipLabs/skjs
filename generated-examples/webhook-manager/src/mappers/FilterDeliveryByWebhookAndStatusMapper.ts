import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  Delivery,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each delivery entry, emit the entry unchanged when the entry's value's webhookId field equals the webhookId param AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterDeliveryByWebhookAndStatusMapper implements Mapper<
  Delivery_skip_id_,
  Delivery_skip_value_,
  Delivery_skip_id_,
  Delivery_skip_value_
> {
  constructor(
    private webhookId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: Delivery_skip_id_,
    values: Values<Delivery_skip_value_>,
    context: Context,
  ): Iterable<[Delivery_skip_id_, Delivery_skip_value_]> {
    // > body
    const emits: [Delivery_skip_id_, Delivery_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (
        value.webhookId === this.webhookId &&
        (this.status === null || value.status === this.status)
      ) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
