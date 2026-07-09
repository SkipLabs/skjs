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

// For each product entry, apply filters in sequence: when the category param is present and the entry's value's category field does not equal the category param, emit nothing; when the search param is present and the entry's value's name field lowercased does not contain the search param lowercased as a substring, emit nothing. Otherwise, consult popularityByProduct for the values indexed by the entry's key. If the consultation yields no values, use zero; otherwise use the first value as the popularity count. Emit one output pair whose key is the entry's key and whose value lists every required field of Product explicitly: id sourced from the entry's key; name sourced from the entry's value's name field; category sourced from the entry's value's category field; price sourced from the entry's value's price field; createdAt sourced from the entry's value's createdAt field; description present when the entry's value has a description field, sourced from the entry's value's description field, absent otherwise; tags present when the entry's value has a tags field, sourced from the entry's value's tags field, absent otherwise; popularity always present, sourced from the resolved popularity count.
export class ListProductsMapper implements Mapper<
  Product_skip_id_,
  ProductStored,
  Product_skip_id_,
  Product
> {
  constructor(
    private popularityByProduct: EagerCollection<
      Product_skip_id_,
      ProductPopularityCount
    >,
    private category: string | null,
    private search: string | null,
  ) {}

  mapEntry(
    key: Product_skip_id_,
    values: Values<ProductStored>,
    context: Context,
  ): Iterable<[Product_skip_id_, Product]> {
    // > body
    const stored = values.toArray()[0];
    if (stored === undefined) return [];
    if (this.category !== null && stored.category !== this.category) return [];
    if (
      this.search !== null &&
      !stored.name.toLowerCase().includes(this.search.toLowerCase())
    )
      return [];
    const popValues = this.popularityByProduct.getArray(key);
    const popularity = popValues.length === 0 ? 0 : (popValues[0] ?? 0);
    const product: Product = {
      id: key,
      name: stored.name,
      category: stored.category,
      price: stored.price,
      createdAt: stored.createdAt,
      ...(stored.description !== undefined && {
        description: stored.description,
      }),
      ...(stored.tags !== undefined && { tags: stored.tags }),
      popularity,
    };
    return [[key, product]];
    // < body
  }
}
