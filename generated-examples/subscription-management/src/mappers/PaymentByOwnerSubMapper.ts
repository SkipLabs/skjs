import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  PaymentEvent,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment event entry, emit the entry unchanged when the entry's value subscriptionId field equals the subscriptionId param AND the entry's value ownerId field equals the userId param. Otherwise emit nothing.
export class PaymentByOwnerSubMapper implements Mapper<
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_
> {
  constructor(
    private subscriptionId: string,
    private userId: string,
  ) {}

  mapEntry(
    key: PaymentEvent_skip_id_,
    values: Values<PaymentEvent_skip_value_>,
    context: Context,
  ): Iterable<[PaymentEvent_skip_id_, PaymentEvent_skip_value_]> {
    // > body
    const emits: [PaymentEvent_skip_id_, PaymentEvent_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (
        value.subscriptionId === this.subscriptionId &&
        value.ownerId === this.userId
      ) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
