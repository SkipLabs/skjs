import { FilterProductBySearchMapper } from "../mappers/FilterProductBySearchMapper.js";
import type {
  Product_skip_id_,
  Product_skip_value_,
  ListProductsParams,
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
  private readonly search: string | null;

  constructor(params: ListProductsParams) {
    this.search = params.search ?? null;
  }

  instantiate(
    inputs: ListProductsResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, Product_skip_value_> {
    return inputs.products.map(FilterProductBySearchMapper, this.search);
  }
}
