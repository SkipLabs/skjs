import type { Sku_skip_id_, Sku_skip_value_, Sku } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetSkuResourceInputs extends SharedCollections {
  readonly skus: EagerCollection<Sku_skip_id_, Sku_skip_value_>;
}

export class GetSkuResource implements Resource<GetSkuResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetSkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Sku_skip_value_> {
    return inputs.skus;
  }
}
