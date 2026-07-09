import { ListProductsMapper } from "../mappers/ListProductsMapper.js";
import type {
  Product_skip_id_,
  ProductPopularityCount,
  ProductStored,
  Product,
  ListProductsParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListProductsResourceInputs extends SharedCollections {
  readonly popularityByProduct: EagerCollection<
    Product_skip_id_,
    ProductPopularityCount
  >;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
}

export class ListProductsResource implements Resource<ListProductsResourceInputs> {
  private readonly category: string | null;
  private readonly search: string | null;

  constructor(params: ListProductsParams) {
    this.category = params.category ?? null;
    this.search = params.search ?? null;
  }

  instantiate(
    inputs: ListProductsResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, Product> {
    return inputs.products.map(
      ListProductsMapper,
      inputs.popularityByProduct,
      this.category,
      this.search,
    );
  }
}
