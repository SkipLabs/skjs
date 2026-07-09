import { FilterProductsMapper } from "../mappers/FilterProductsMapper.js";
import type {
  Product_skip_id_,
  ProductStored,
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
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
}

export class ListProductsResource implements Resource<ListProductsResourceInputs> {
  private readonly categoryId: string | null;
  private readonly inStock: boolean | null;
  private readonly ownerId: string | null;
  private readonly search: string | null;

  constructor(params: ListProductsParams) {
    this.categoryId = params.categoryId ?? null;
    this.inStock = params.inStock ?? null;
    this.ownerId = params.ownerId ?? null;
    this.search = params.search ?? null;
  }

  instantiate(
    inputs: ListProductsResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, ProductStored> {
    return inputs.products.map(
      FilterProductsMapper,
      this.categoryId,
      this.ownerId,
      this.search,
      this.inStock,
    );
  }
}
