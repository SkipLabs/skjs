import { GetProductMapper } from "../mappers/GetProductMapper.js";
import type {
  Product_skip_id_,
  ProductPopularityCount,
  ProductStored,
  Product,
  GetProductParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetProductResourceInputs extends SharedCollections {
  readonly popularityByProduct: EagerCollection<
    Product_skip_id_,
    ProductPopularityCount
  >;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
}

export class GetProductResource implements Resource<GetProductResourceInputs> {
  private readonly productId: string;

  constructor(params: GetProductParams) {
    this.productId = params.productId;
  }

  instantiate(
    inputs: GetProductResourceInputs,
    _context: Context,
  ): EagerCollection<Product_skip_id_, Product> {
    return inputs.products.map(
      GetProductMapper,
      this.productId,
      inputs.popularityByProduct,
    );
  }
}
