import type {
  Binding_skip_id_,
  Binding_skip_value_,
  Binding,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBindingResourceInputs extends SharedCollections {
  readonly bindings: EagerCollection<Binding_skip_id_, Binding_skip_value_>;
}

export class GetBindingResource implements Resource<GetBindingResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetBindingResourceInputs,
    _context: Context,
  ): EagerCollection<Binding_skip_id_, Binding_skip_value_> {
    return inputs.bindings;
  }
}
