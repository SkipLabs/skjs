import type { Webhook_skip_id_, WebhookStored, Webhook } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetWebhookResourceInputs extends SharedCollections {
  readonly webhooks: EagerCollection<Webhook_skip_id_, WebhookStored>;
}

export class GetWebhookResource implements Resource<GetWebhookResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetWebhookResourceInputs,
    _context: Context,
  ): EagerCollection<Webhook_skip_id_, WebhookStored> {
    return inputs.webhooks;
  }
}
