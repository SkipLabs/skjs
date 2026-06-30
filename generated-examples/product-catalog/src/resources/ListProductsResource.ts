import type {
  Product_skip_id_,
  Product_skip_value_,
  Product,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListProductsResourceInputs extends SharedCollections {
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
}

export class ListProductsResource implements Resource<ListProductsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListProductsResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, Product_skip_value_> {
    return inputs.products;
  }
}
