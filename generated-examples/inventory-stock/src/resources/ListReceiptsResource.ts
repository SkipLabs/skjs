import { ReceiptByOwnerMapper } from "../mappers/ReceiptByOwnerMapper.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  User_skip_id_,
  Receipt,
  ListReceiptsParams,
  User,
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
  private readonly userId: string;

  constructor(params: ListReceiptsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListReceiptsResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Receipt> {
    return inputs.receipts.map(ReceiptByOwnerMapper, this.userId);
  }
}
