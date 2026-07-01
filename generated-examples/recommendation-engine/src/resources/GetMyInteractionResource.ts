import { GetMyInteractionMapper } from "../mappers/GetMyInteractionMapper.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  GetMyInteractionParams,
  Interaction,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMyInteractionResourceInputs extends SharedCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
}

export class GetMyInteractionResource implements Resource<GetMyInteractionResourceInputs> {
  private readonly interactionId: string;
  private readonly userId: string;

  constructor(params: GetMyInteractionParams) {
    this.interactionId = params.interactionId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMyInteractionResourceInputs,
    _context: Context,
  ): EagerCollection<Interaction_skip_id_, Interaction_skip_value_> {
    return inputs.interactions.map(
      GetMyInteractionMapper,
      this.userId,
      this.interactionId,
    );
  }
}
