import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Webhook_skip_id_, WebhookStored, Webhook } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each webhook entry, emit the entry unchanged when the entry's value's ownerId field equals the userId param AND (the active param is absent OR the entry's value's active field equals the active param). Otherwise emit nothing.
export class FilterWebhookByOwnerAndActiveMapper implements Mapper<
  Webhook_skip_id_,
  WebhookStored,
  Webhook_skip_id_,
  WebhookStored
> {
  constructor(
    private userId: string,
    private active: boolean | null,
  ) {}

  mapEntry(
    key: Webhook_skip_id_,
    values: Values<WebhookStored>,
    context: Context,
  ): Iterable<[Webhook_skip_id_, WebhookStored]> {
    // > body
    const emits: [Webhook_skip_id_, WebhookStored][] = [];
    for (const value of values.toArray()) {
      if (
        value.ownerId === this.userId &&
        (this.active === null || value.active === this.active)
      ) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
