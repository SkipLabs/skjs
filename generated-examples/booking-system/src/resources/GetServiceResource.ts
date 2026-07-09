import type {
  Service_skip_id_,
  Service_skip_value_,
  Service,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetServiceResourceInputs extends SharedCollections {
  readonly services: EagerCollection<Service_skip_id_, Service_skip_value_>;
}

export class GetServiceResource implements Resource<GetServiceResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetServiceResourceInputs,
    _context: Context,
  ): EagerCollection<Service_skip_id_, Service_skip_value_> {
    return inputs.services;
  }
}
