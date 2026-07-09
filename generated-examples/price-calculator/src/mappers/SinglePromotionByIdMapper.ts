import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each promotion entry, emit the entry unchanged when the entry's key equals the promotionId param. Otherwise emit nothing.
export class SinglePromotionByIdMapper implements Mapper<
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion_skip_id_,
  Promotion_skip_value_
> {
  constructor(private promotionId: string) {}

  mapEntry(
    key: Promotion_skip_id_,
    values: Values<Promotion_skip_value_>,
    context: Context,
  ): Iterable<[Promotion_skip_id_, Promotion_skip_value_]> {
    // > body
    if (key === this.promotionId) {
      const emits: [Promotion_skip_id_, Promotion_skip_value_][] = [];
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
      return emits;
    }
    return [];
    // < body
  }
}
