import type { Product_skip_id_, ProductStored, Product } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetProductStoredResourceInputs extends SharedCollections {
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
}

export class GetProductStoredResource implements Resource<GetProductStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetProductStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, ProductStored> {
    return inputs.products;
  }
}
