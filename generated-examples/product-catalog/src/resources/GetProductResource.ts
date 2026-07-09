import type { Product_skip_id_, ProductStored, Product } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetProductResourceInputs extends SharedCollections {
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
}

export class GetProductResource implements Resource<GetProductResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetProductResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, ProductStored> {
    return inputs.products;
  }
}
