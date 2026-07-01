import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPromotionResourceInputs extends SharedCollections {
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
}

export class GetPromotionResource implements Resource<GetPromotionResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPromotionResourceInputs,
    _context: Context,
  ): EagerCollection<Promotion_skip_id_, Promotion_skip_value_> {
    return inputs.promotions;
  }
}
