import { FilterSkuBySearchMapper } from "../mappers/FilterSkuBySearchMapper.js";
import type {
  Sku_skip_id_,
  Sku_skip_value_,
  ListSkusParams,
  Sku,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListSkusResourceInputs extends SharedCollections {
  readonly skus: EagerCollection<Sku_skip_id_, Sku_skip_value_>;
}

export class ListSkusResource implements Resource<ListSkusResourceInputs> {
  private readonly search: string | null;

  constructor(params: ListSkusParams) {
    this.search = params.search ?? null;
  }

  instantiate(
    inputs: ListSkusResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Sku_skip_value_> {
    return inputs.skus.map(FilterSkuBySearchMapper, this.search);
  }
}
