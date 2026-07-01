import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Product_skip_id_,
  Product_skip_value_,
  Product,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each product entry, emit the entry unchanged when (the categoryId param is absent OR the entry's categoryId field equals the categoryId param) AND (the q param is absent OR the entry's name field, lowercased, contains the q param, lowercased, as a substring). Otherwise emit nothing.
export class FilterProductsMapper implements Mapper<
  Product_skip_id_,
  Product_skip_value_,
  Product_skip_id_,
  Product_skip_value_
> {
  constructor(
    private categoryId: string | null,
    private q: string | null,
  ) {}

  mapEntry(
    key: Product_skip_id_,
    values: Values<Product_skip_value_>,
    context: Context,
  ): Iterable<[Product_skip_id_, Product_skip_value_]> {
    // > body
    const emits: [Product_skip_id_, Product_skip_value_][] = [];
    const qLower = this.q !== null ? this.q.toLowerCase() : null;
    for (const value of values.toArray()) {
      if (this.categoryId !== null && value.categoryId !== this.categoryId)
        continue;
      if (qLower !== null && !value.name.toLowerCase().includes(qLower))
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
