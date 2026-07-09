import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Customer_skip_id_,
  CustomerStored,
  Customer_skip_value_,
  Customer,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each customer entry, emit one output pair whose key is the entry's key and whose value lists every required field of Customer_skip_value_ explicitly: ownerId sourced from the entry's value's ownerId field; name sourced from the entry's value's name field; createdAt sourced from the entry's value's createdAt field. Optional fields: email (present when the entry's value's email field is present, sourced from the entry's value's email field; absent otherwise); phone (present when the entry's value's phone field is present, sourced from the entry's value's phone field; absent otherwise); billingAddress (present when the entry's value's billingAddress field is present, sourced from the entry's value's billingAddress field; absent otherwise); notes (present when the entry's value's notes field is present, sourced from the entry's value's notes field; absent otherwise); updatedAt (present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field; absent otherwise).
export class AssembleCustomerMapper implements Mapper<
  Customer_skip_id_,
  CustomerStored,
  Customer_skip_id_,
  Customer_skip_value_
> {
  mapEntry(
    key: Customer_skip_id_,
    values: Values<CustomerStored>,
    context: Context,
  ): Iterable<[Customer_skip_id_, Customer_skip_value_]> {
    // > body
    const emits: [Customer_skip_id_, Customer_skip_value_][] = [];
    for (const value of values.toArray()) {
      const out: Customer_skip_value_ = {
        ownerId: value.ownerId,
        name: value.name,
        createdAt: value.createdAt,
        ...(value.email !== undefined && { email: value.email }),
        ...(value.phone !== undefined && { phone: value.phone }),
        ...(value.billingAddress !== undefined && {
          billingAddress: value.billingAddress,
        }),
        ...(value.notes !== undefined && { notes: value.notes }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
