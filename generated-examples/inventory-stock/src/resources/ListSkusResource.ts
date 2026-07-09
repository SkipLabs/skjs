import { SkuByOwnerFullMapper } from "../mappers/SkuByOwnerFullMapper.js";
import type {
  Sku_skip_id_,
  Sku_skip_value_,
  User_skip_id_,
  Sku,
  ListSkusParams,
  User,
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
  private readonly userId: string;

  constructor(params: ListSkusParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListSkusResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Sku> {
    return inputs.skus.map(SkuByOwnerFullMapper, this.userId);
  }
}
