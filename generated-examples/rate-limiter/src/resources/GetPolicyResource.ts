import type { Policy_skip_id_, Policy_skip_value_, Policy } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPolicyResourceInputs extends SharedCollections {
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
}

export class GetPolicyResource implements Resource<GetPolicyResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPolicyResourceInputs,
    _context: Context,
  ): EagerCollection<Policy_skip_id_, Policy_skip_value_> {
    return inputs.policies;
  }
}
