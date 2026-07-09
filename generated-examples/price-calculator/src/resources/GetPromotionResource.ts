import { SinglePromotionByIdMapper } from "../mappers/SinglePromotionByIdMapper.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  GetPromotionParams,
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
  private readonly promotionId: string;

  constructor(params: GetPromotionParams) {
    this.promotionId = params.promotionId;
  }

  instantiate(
    inputs: GetPromotionResourceInputs,
    _context: Context,
  ): EagerCollection<Promotion_skip_id_, Promotion_skip_value_> {
    return inputs.promotions.map(SinglePromotionByIdMapper, this.promotionId);
  }
}
