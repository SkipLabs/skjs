import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  Product_skip_id_,
  ProductPopularityCount,
  Interaction,
  Product,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit one output pair when the entry's value's type field equals the literal 'PURCHASE': the output key is sourced from the entry's value's productId field and the output value is the literal 1. Otherwise emit nothing. The original Interaction.id is dropped: this mapper feeds SumReducer which aggregates purchase counts per product and never needs to identify the source Interaction row.
export class PurchaseInteractionMapper implements Mapper<
  Interaction_skip_id_,
  Interaction_skip_value_,
  Product_skip_id_,
  ProductPopularityCount
> {
  mapEntry(
    key: Interaction_skip_id_,
    values: Values<Interaction_skip_value_>,
    context: Context,
  ): Iterable<[Product_skip_id_, ProductPopularityCount]> {
    // > body
    const emits: [Product_skip_id_, ProductPopularityCount][] = [];
    for (const value of values.toArray()) {
      if (value.type === "PURCHASE") {
        emits.push([value.productId, 1]);
      }
    }
    return emits;
    // < body
  }
}
