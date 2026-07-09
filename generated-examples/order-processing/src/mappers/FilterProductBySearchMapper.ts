import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Product_skip_id_,
  Product_skip_value_,
  Product,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each product entry, when the search param is absent, emit the entry unchanged. Otherwise, emit the entry unchanged when the entry's name field, lowercased, contains the search param, lowercased, as a substring. Otherwise emit nothing.
export class FilterProductBySearchMapper implements Mapper<
  Product_skip_id_,
  Product_skip_value_,
  Product_skip_id_,
  Product_skip_value_
> {
  constructor(private search: string | null) {}

  mapEntry(
    key: Product_skip_id_,
    values: Values<Product_skip_value_>,
    context: Context,
  ): Iterable<[Product_skip_id_, Product_skip_value_]> {
    // > body
    const emits: [Product_skip_id_, Product_skip_value_][] = [];
    const search = this.search;
    if (search === null) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    } else {
      const needle = search.toLowerCase();
      for (const value of values.toArray()) {
        if (value.name.toLowerCase().includes(needle)) {
          emits.push([key, value]);
        }
      }
    }
    return emits;
    // < body
  }
}
