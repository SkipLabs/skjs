import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Sku_skip_id_, Sku_skip_value_, Sku } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each sku entry, when the search param is absent emit the entry unchanged. Otherwise, emit the entry unchanged when the entry's code field, lowercased, contains the search param, lowercased, as a substring; emit nothing otherwise.
export class FilterSkuBySearchMapper implements Mapper<
  Sku_skip_id_,
  Sku_skip_value_,
  Sku_skip_id_,
  Sku_skip_value_
> {
  constructor(private search: string | null) {}

  mapEntry(
    key: Sku_skip_id_,
    values: Values<Sku_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, Sku_skip_value_]> {
    // > body
    const search = this.search;
    const emits: [Sku_skip_id_, Sku_skip_value_][] = [];
    if (search === null) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
      return emits;
    }
    const needle = search.toLowerCase();
    for (const value of values.toArray()) {
      if (value.code.toLowerCase().includes(needle)) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
