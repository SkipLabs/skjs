import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Product_skip_id_, ProductStored, Product } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each product entry, emit the entry unchanged when ALL of the following hold: (the categoryId param is absent OR the entry's categoryId field equals the categoryId param); AND (the ownerId param is absent OR the entry's ownerId field equals the ownerId param); AND (the search param is absent OR the entry's name field, lowercased, contains the search param, lowercased, as a substring); AND (the inStock param is absent OR (the inStock param is true AND the entry's stockQuantity field is strictly greater than 0) OR (the inStock param is false AND the entry's stockQuantity field equals 0)). Otherwise emit nothing.
export class FilterProductsMapper implements Mapper<
  Product_skip_id_,
  ProductStored,
  Product_skip_id_,
  ProductStored
> {
  constructor(
    private categoryId: string | null,
    private ownerId: string | null,
    private search: string | null,
    private inStock: boolean | null,
  ) {}

  mapEntry(
    key: Product_skip_id_,
    values: Values<ProductStored>,
    context: Context,
  ): Iterable<[Product_skip_id_, ProductStored]> {
    // > body
    const emits: [Product_skip_id_, ProductStored][] = [];
    for (const value of values.toArray()) {
      if (this.categoryId !== null && value.categoryId !== this.categoryId)
        continue;
      if (this.ownerId !== null && value.ownerId !== this.ownerId) continue;
      if (
        this.search !== null &&
        !value.name.toLowerCase().includes(this.search.toLowerCase())
      )
        continue;
      if (this.inStock !== null) {
        if (this.inStock === true && !(value.stockQuantity > 0)) continue;
        if (this.inStock === false && value.stockQuantity !== 0) continue;
      }
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
