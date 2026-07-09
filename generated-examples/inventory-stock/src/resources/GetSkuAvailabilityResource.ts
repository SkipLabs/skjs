import type { Sku_skip_id_, SkuAvailability, Sku } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetSkuAvailabilityResourceInputs extends SharedCollections {
  readonly skuAvailability: EagerCollection<Sku_skip_id_, SkuAvailability>;
}

export class GetSkuAvailabilityResource implements Resource<GetSkuAvailabilityResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetSkuAvailabilityResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, SkuAvailability> {
    return inputs.skuAvailability;
  }
}
