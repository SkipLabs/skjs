import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Product_skip_id_,
  ProductStored,
  Product,
  ProductPopularityCount,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each product entry, emit nothing when the entry's key does not equal the productId param. Otherwise, consult popularityByProduct for the values indexed by the entry's key. If the consultation yields no values, use zero; otherwise use the first value as the popularity count. Emit one output pair whose key is the entry's key and whose value lists every required field of Product explicitly: id sourced from the entry's key; name sourced from the entry's value's name field; category sourced from the entry's value's category field; price sourced from the entry's value's price field; createdAt sourced from the entry's value's createdAt field; description present when the entry's value has a description field, sourced from the entry's value's description field, absent otherwise; tags present when the entry's value has a tags field, sourced from the entry's value's tags field, absent otherwise; popularity always present, sourced from the resolved popularity count (zero when the consultation yielded no values).
export class GetProductMapper implements Mapper<
  Product_skip_id_,
  ProductStored,
  Product_skip_id_,
  Product
> {
  constructor(
    private productId: string,
    private popularityByProduct: EagerCollection<
      Product_skip_id_,
      ProductPopularityCount
    >,
  ) {}

  mapEntry(
    key: Product_skip_id_,
    values: Values<ProductStored>,
    context: Context,
  ): Iterable<[Product_skip_id_, Product]> {
    // > body
    if (key !== this.productId) return [];
    const value = values.toArray()[0];
    if (value === undefined) return [];
    const popularityValues = this.popularityByProduct.getArray(key);
    const popularity =
      popularityValues.length === 0 ? 0 : (popularityValues[0] ?? 0);
    const product: Product = {
      id: key,
      name: value.name,
      category: value.category,
      price: value.price,
      createdAt: value.createdAt,
      ...(value.description !== undefined && {
        description: value.description,
      }),
      ...(value.tags !== undefined && { tags: value.tags }),
      popularity,
    };
    return [[key, product]];
    // < body
  }
}
