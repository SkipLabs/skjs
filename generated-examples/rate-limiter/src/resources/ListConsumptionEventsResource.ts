import { FilterEventsByPolicyMapper } from "../mappers/FilterEventsByPolicyMapper.js";
import type {
  Policy_skip_id_,
  ConsumptionEvent,
  ListConsumptionEventsParams,
  Policy,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListConsumptionEventsResourceInputs extends SharedCollections {
  readonly eventsByPolicy: EagerCollection<Policy_skip_id_, ConsumptionEvent>;
}

export class ListConsumptionEventsResource implements Resource<ListConsumptionEventsResourceInputs> {
  private readonly policyId: string;

  constructor(params: ListConsumptionEventsParams) {
    this.policyId = params.policyId;
  }

  instantiate(
    inputs: ListConsumptionEventsResourceInputs,
    _context: Context,
  ): EagerCollection<Policy_skip_id_, ConsumptionEvent> {
    return inputs.eventsByPolicy.map(FilterEventsByPolicyMapper, this.policyId);
  }
}
