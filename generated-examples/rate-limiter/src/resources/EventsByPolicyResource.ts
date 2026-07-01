import type { Policy_skip_id_, ConsumptionEvent, Policy } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface EventsByPolicyResourceInputs extends SharedCollections {
  readonly eventsByPolicy: EagerCollection<Policy_skip_id_, ConsumptionEvent>;
}

export class EventsByPolicyResource implements Resource<EventsByPolicyResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: EventsByPolicyResourceInputs,
    _context: Context,
  ): EagerCollection<Policy_skip_id_, ConsumptionEvent> {
    return inputs.eventsByPolicy;
  }
}
