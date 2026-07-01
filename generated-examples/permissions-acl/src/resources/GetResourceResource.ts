import type {
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_,
  ProtectedResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetResourceResourceInputs extends SharedCollections {
  readonly resources: EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  >;
}

export class GetResourceResource implements Resource<GetResourceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetResourceResourceInputs,
    _context: Context,
  ): EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  > {
    return inputs.resources;
  }
}
