import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  Interaction,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetInteractionResourceInputs extends SharedCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
}

export class GetInteractionResource implements Resource<GetInteractionResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetInteractionResourceInputs,
    _context: Context,
  ): EagerCollection<Interaction_skip_id_, Interaction_skip_value_> {
    return inputs.interactions;
  }
}
