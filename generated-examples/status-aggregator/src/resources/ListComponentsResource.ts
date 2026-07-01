import { FilterComponentsByStatusMapper } from "../mappers/FilterComponentsByStatusMapper.js";
import type {
  Component_skip_id_,
  ComponentStored,
  ComponentStatus,
  ListComponentsParams,
  Component,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListComponentsResourceInputs extends SharedCollections {
  readonly components: EagerCollection<Component_skip_id_, ComponentStored>;
}

export class ListComponentsResource implements Resource<ListComponentsResourceInputs> {
  private readonly status: ComponentStatus | null;

  constructor(params: ListComponentsParams) {
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListComponentsResourceInputs,
    _context: Context,
  ): EagerCollection<Component_skip_id_, ComponentStored> {
    return inputs.components.map(FilterComponentsByStatusMapper, this.status);
  }
}
