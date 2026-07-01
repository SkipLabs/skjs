import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  Webhook_skip_id_,
  Delivery,
  Webhook,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each delivery entry, emit one output pair whose key is sourced from the entry's value's webhookId field, paired with a new value listing every required field of Delivery explicitly: id sourced from the entry's key, webhookId sourced from the entry's value's webhookId field, eventType sourced from the entry's value's eventType field, payload sourced from the entry's value's payload field, status sourced from the entry's value's status field, attemptCount sourced from the entry's value's attemptCount field, and attemptedAt sourced from the entry's value's attemptedAt field. Optional fields (responseStatusCode, responseBody, errorMessage) are copied from the entry's value when present.
export class DeliveryByWebhookMapper implements Mapper<
  Delivery_skip_id_,
  Delivery_skip_value_,
  Webhook_skip_id_,
  Delivery
> {
  mapEntry(
    key: Delivery_skip_id_,
    values: Values<Delivery_skip_value_>,
    context: Context,
  ): Iterable<[Webhook_skip_id_, Delivery]> {
    // > body
    const emits: [Webhook_skip_id_, Delivery][] = [];
    for (const value of values.toArray()) {
      const delivery: Delivery = {
        id: key,
        webhookId: value.webhookId,
        eventType: value.eventType,
        payload: value.payload,
        status: value.status,
        attemptCount: value.attemptCount,
        attemptedAt: value.attemptedAt,
        ...(value.responseStatusCode !== undefined && {
          responseStatusCode: value.responseStatusCode,
        }),
        ...(value.responseBody !== undefined && {
          responseBody: value.responseBody,
        }),
        ...(value.errorMessage !== undefined && {
          errorMessage: value.errorMessage,
        }),
      };
      emits.push([value.webhookId, delivery]);
    }
    return emits;
    // < body
  }
}
