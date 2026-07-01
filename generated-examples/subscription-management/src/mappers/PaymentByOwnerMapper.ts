import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  User_skip_id_,
  PaymentEvent,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment event entry, emit one output pair whose key is sourced from the entry's value ownerId field (which is the User primary key — JWT sub claim of the owner), paired with a new value listing every required field of PaymentEvent explicitly: id is sourced from the entry's key (= the original PaymentEvent.id, preserved on the value side); subscriptionId, ownerId, amountCents, currency, paidAt, createdAt are sourced from the entry's value; optional fields method, notes are sourced from the entry's value when present and omitted otherwise. The original PaymentEvent.id is preserved in the value as the id field — the cascade-delete handler iterating per-owner payments can recover each payment's id from the value.
export class PaymentByOwnerMapper implements Mapper<
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  User_skip_id_,
  PaymentEvent
> {
  mapEntry(
    key: PaymentEvent_skip_id_,
    values: Values<PaymentEvent_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, PaymentEvent]> {
    // > body
    const emits: [User_skip_id_, PaymentEvent][] = [];
    for (const value of values.toArray()) {
      const event: PaymentEvent = {
        id: key,
        subscriptionId: value.subscriptionId,
        ownerId: value.ownerId,
        amountCents: value.amountCents,
        currency: value.currency,
        paidAt: value.paidAt,
        createdAt: value.createdAt,
        ...(value.method !== undefined && { method: value.method }),
        ...(value.notes !== undefined && { notes: value.notes }),
      };
      emits.push([value.ownerId, event]);
    }
    return emits;
    // < body
  }
}
