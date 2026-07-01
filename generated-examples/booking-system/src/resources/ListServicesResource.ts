import { FilterServiceByProviderMapper } from "../mappers/FilterServiceByProviderMapper.js";
import type {
  Service_skip_id_,
  Service_skip_value_,
  ListServicesParams,
  Service,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListServicesResourceInputs extends SharedCollections {
  readonly services: EagerCollection<Service_skip_id_, Service_skip_value_>;
}

export class ListServicesResource implements Resource<ListServicesResourceInputs> {
  private readonly providerId: string | null;

  constructor(params: ListServicesParams) {
    this.providerId = params.providerId ?? null;
  }

  instantiate(
    inputs: ListServicesResourceInputs,
    _context: Context,
  ): EagerCollection<Service_skip_id_, Service_skip_value_> {
    return inputs.services.map(FilterServiceByProviderMapper, this.providerId);
  }
}
