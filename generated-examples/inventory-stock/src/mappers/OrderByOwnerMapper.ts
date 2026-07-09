import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
  User_skip_id_,
  Order,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order entry, emit one output pair when the entry's value's ownerId field equals the userId param, otherwise emit nothing. The output key is the userId param. The output value lists every required field of Order explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; skuId sourced from the entry's value's skuId field; quantity sourced from the entry's value's quantity field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field. Optional fields: customerRef is present when the entry's value's customerRef field is present, sourced from that field; absent otherwise. allocatedAt is present when the entry's value's allocatedAt field is present, sourced from that field; absent otherwise. fulfilledAt is present when the entry's value's fulfilledAt field is present, sourced from that field; absent otherwise. cancelledAt is present when the entry's value's cancelledAt field is present, sourced from that field; absent otherwise.
export class OrderByOwnerMapper implements Mapper<
  Order_skip_id_,
  Order_skip_value_,
  User_skip_id_,
  Order
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Order_skip_id_,
    values: Values<Order_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Order]> {
    // > body
    const emits: [User_skip_id_, Order][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      const order: Order = {
        id: key,
        ownerId: value.ownerId,
        skuId: value.skuId,
        quantity: value.quantity,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.customerRef !== undefined && {
          customerRef: value.customerRef,
        }),
        ...(value.allocatedAt !== undefined && {
          allocatedAt: value.allocatedAt,
        }),
        ...(value.fulfilledAt !== undefined && {
          fulfilledAt: value.fulfilledAt,
        }),
        ...(value.cancelledAt !== undefined && {
          cancelledAt: value.cancelledAt,
        }),
      };
      emits.push([this.userId, order]);
    }
    return emits;
    // < body
  }
}
