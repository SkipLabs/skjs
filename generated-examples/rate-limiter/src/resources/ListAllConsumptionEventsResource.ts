import type {
  ConsumptionEvent_skip_id_,
  ConsumptionEvent_skip_value_,
  ConsumptionEvent,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListAllConsumptionEventsResourceInputs extends SharedCollections {
  readonly consumptionEvents: EagerCollection<
    ConsumptionEvent_skip_id_,
    ConsumptionEvent_skip_value_
  >;
}

export class ListAllConsumptionEventsResource implements Resource<ListAllConsumptionEventsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListAllConsumptionEventsResourceInputs,
    _context: Context,
  ): EagerCollection<ConsumptionEvent_skip_id_, ConsumptionEvent_skip_value_> {
    return inputs.consumptionEvents;
  }
}
