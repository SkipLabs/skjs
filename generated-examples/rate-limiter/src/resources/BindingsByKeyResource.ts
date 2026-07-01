import type { ApiKey_skip_id_, Binding, ApiKey } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface BindingsByKeyResourceInputs extends SharedCollections {
  readonly bindingsByKey: EagerCollection<ApiKey_skip_id_, Binding>;
}

export class BindingsByKeyResource implements Resource<BindingsByKeyResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: BindingsByKeyResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, Binding> {
    return inputs.bindingsByKey;
  }
}
