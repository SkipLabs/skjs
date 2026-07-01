import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  User_skip_id_,
  Receipt,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each receipt entry, emit one output pair when the entry's value's ownerId field equals the userId param, otherwise emit nothing. The output key is the userId param. The output value lists every required field of Receipt explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; skuId sourced from the entry's value's skuId field; quantity sourced from the entry's value's quantity field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field. Optional fields: note is present when the entry's value's note field is present, sourced from that field; absent otherwise. receivedAt is present when the entry's value's receivedAt field is present, sourced from that field; absent otherwise.
export class ReceiptByOwnerMapper implements Mapper<
  Receipt_skip_id_,
  Receipt_skip_value_,
  User_skip_id_,
  Receipt
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Receipt_skip_id_,
    values: Values<Receipt_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Receipt]> {
    // > body
    const emits: [User_skip_id_, Receipt][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      const receipt: Receipt = {
        id: key,
        ownerId: value.ownerId,
        skuId: value.skuId,
        quantity: value.quantity,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
        ...(value.receivedAt !== undefined && { receivedAt: value.receivedAt }),
      };
      emits.push([this.userId, receipt]);
    }
    return emits;
    // < body
  }
}
