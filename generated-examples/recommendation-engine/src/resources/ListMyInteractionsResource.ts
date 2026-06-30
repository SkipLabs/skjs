import { FilterMyInteractionsMapper } from "../mappers/FilterMyInteractionsMapper.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  ListMyInteractionsParams,
  Interaction,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyInteractionsResourceInputs extends SharedCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
}

export class ListMyInteractionsResource implements Resource<ListMyInteractionsResourceInputs> {
  private readonly productId: string | null;
  private readonly type: string | null;
  private readonly userId: string;

  constructor(params: ListMyInteractionsParams) {
    this.productId = params.productId ?? null;
    this.type = params.type ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyInteractionsResourceInputs,
    _context: Context,
  ): EagerCollection<Interaction_skip_id_, Interaction_skip_value_> {
    return inputs.interactions.map(
      FilterMyInteractionsMapper,
      this.userId,
      this.type,
      this.productId,
    );
  }
}
