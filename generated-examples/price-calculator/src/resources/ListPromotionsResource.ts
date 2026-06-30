import { FilterPromotionByActiveMapper } from "../mappers/FilterPromotionByActiveMapper.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  ListPromotionsParams,
  Promotion,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPromotionsResourceInputs extends SharedCollections {
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
}

export class ListPromotionsResource implements Resource<ListPromotionsResourceInputs> {
  private readonly active: boolean | null;

  constructor(params: ListPromotionsParams) {
    this.active = params.active ?? null;
  }

  instantiate(
    inputs: ListPromotionsResourceInputs,
    _context: Context,
  ): EagerCollection<Promotion_skip_id_, Promotion_skip_value_> {
    return inputs.promotions.map(FilterPromotionByActiveMapper, this.active);
  }
}
