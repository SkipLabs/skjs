import { InteractionByUserMapper } from "../mappers/InteractionByUserMapper.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  User_skip_id_,
  Interaction,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface InteractionsByUserResourceInputs extends SharedCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
}

export class InteractionsByUserResource implements Resource<InteractionsByUserResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: InteractionsByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Interaction> {
    const interactionsByUser = inputs.interactions.map(InteractionByUserMapper);
    return interactionsByUser;
  }
}
