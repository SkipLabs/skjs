import type {
  Component_skip_id_,
  ComponentStored,
  Component,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetComponentResourceInputs extends SharedCollections {
  readonly components: EagerCollection<Component_skip_id_, ComponentStored>;
}

export class GetComponentResource implements Resource<GetComponentResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetComponentResourceInputs,
    _context: Context,
  ): EagerCollection<Component_skip_id_, ComponentStored> {
    return inputs.components;
  }
}
