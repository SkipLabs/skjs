import { FilterUsageEventsByKeyIdMapper } from "../mappers/FilterUsageEventsByKeyIdMapper.js";
import type {
  ApiKey_skip_id_,
  UsageEvent,
  ListUsageEventsForApiKeyParams,
  ApiKey,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListUsageEventsForApiKeyResourceInputs extends SharedCollections {
  readonly usageByKey: EagerCollection<ApiKey_skip_id_, UsageEvent>;
}

export class ListUsageEventsForApiKeyResource implements Resource<ListUsageEventsForApiKeyResourceInputs> {
  private readonly keyId: string;

  constructor(params: ListUsageEventsForApiKeyParams) {
    this.keyId = params.keyId;
  }

  instantiate(
    inputs: ListUsageEventsForApiKeyResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, UsageEvent> {
    return inputs.usageByKey.map(FilterUsageEventsByKeyIdMapper, this.keyId);
  }
}
