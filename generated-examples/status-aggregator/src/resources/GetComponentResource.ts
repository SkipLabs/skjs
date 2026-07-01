import type {
  Component_skip_id_,
  Component_skip_value_,
  Component,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetComponentResourceInputs extends SharedCollections {
  readonly components: EagerCollection<
    Component_skip_id_,
    Component_skip_value_
  >;
}

export class GetComponentResource implements Resource<GetComponentResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetComponentResourceInputs,
    _context: Context,
  ): EagerCollection<Component_skip_id_, Component_skip_value_> {
    return inputs.components;
  }
}
