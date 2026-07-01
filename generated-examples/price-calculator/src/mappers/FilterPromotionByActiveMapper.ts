import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit the entry unchanged when the active param is absent OR the entry's active field (defaulted to false when absent) equals the active param. Otherwise emit nothing.
export class FilterPromotionByActiveMapper implements Mapper<
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion_skip_id_,
  Promotion_skip_value_
> {
  constructor(private active: boolean | null) {}

  mapEntry(
    key: Promotion_skip_id_,
    values: Values<Promotion_skip_value_>,
    context: Context,
  ): Iterable<[Promotion_skip_id_, Promotion_skip_value_]> {
    // > body
    const emits: [Promotion_skip_id_, Promotion_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.active === null) {
        emits.push([key, value]);
      } else {
        const entryActive = value.active ?? false;
        if (entryActive === this.active) {
          emits.push([key, value]);
        }
      }
    }
    return emits;
    // < body
  }
}
