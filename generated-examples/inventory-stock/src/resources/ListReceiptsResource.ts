import { FilterReceiptBySkuMapper } from "../mappers/FilterReceiptBySkuMapper.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  ListReceiptsParams,
  Receipt,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReceiptsResourceInputs extends SharedCollections {
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
}

export class ListReceiptsResource implements Resource<ListReceiptsResourceInputs> {
  private readonly skuId: string | null;

  constructor(params: ListReceiptsParams) {
    this.skuId = params.skuId ?? null;
  }

  instantiate(
    inputs: ListReceiptsResourceInputs,
    _context: Context,
  ): EagerCollection<Receipt_skip_id_, Receipt_skip_value_> {
    return inputs.receipts.map(FilterReceiptBySkuMapper, this.skuId);
  }
}
