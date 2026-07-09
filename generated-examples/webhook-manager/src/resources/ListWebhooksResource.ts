import { FilterWebhookByOwnerAndActiveMapper } from "../mappers/FilterWebhookByOwnerAndActiveMapper.js";
import type {
  Webhook_skip_id_,
  WebhookStored,
  ListWebhooksParams,
  Webhook,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListWebhooksResourceInputs extends SharedCollections {
  readonly webhooks: EagerCollection<Webhook_skip_id_, WebhookStored>;
}

export class ListWebhooksResource implements Resource<ListWebhooksResourceInputs> {
  private readonly active: boolean | null;
  private readonly userId: string;

  constructor(params: ListWebhooksParams) {
    this.active = params.active ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListWebhooksResourceInputs,
    _context: Context,
  ): EagerCollection<Webhook_skip_id_, WebhookStored> {
    return inputs.webhooks.map(
      FilterWebhookByOwnerAndActiveMapper,
      this.userId,
      this.active,
    );
  }
}
