import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each promotion entry, when the activeOnly param is absent or is the literal false, emit the entry unchanged. Otherwise (activeOnly is the literal true), emit the entry unchanged when the entry's value's active field equals the literal true; emit nothing when it equals the literal false.
export class FilterPromotionActiveMapper implements Mapper<
  Promotion_skip_id_,
  Promotion_skip_value_,
  Promotion_skip_id_,
  Promotion_skip_value_
> {
  constructor(private activeOnly: boolean | null) {}

  mapEntry(
    key: Promotion_skip_id_,
    values: Values<Promotion_skip_value_>,
    context: Context,
  ): Iterable<[Promotion_skip_id_, Promotion_skip_value_]> {
    // > body
    const emits: [Promotion_skip_id_, Promotion_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.activeOnly === true) {
        if (value.active === true) {
          emits.push([key, value]);
        }
      } else {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
