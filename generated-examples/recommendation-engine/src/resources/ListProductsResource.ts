import { FilterProductsMapper } from "../mappers/FilterProductsMapper.js";
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
  private readonly categoryId: string | null;
  private readonly q: string | null;

  constructor(params: ListProductsParams) {
    this.categoryId = params.categoryId ?? null;
    this.q = params.q ?? null;
  }

  instantiate(
    inputs: ListProductsResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, Product_skip_value_> {
    return inputs.products.map(FilterProductsMapper, this.categoryId, this.q);
  }
}
