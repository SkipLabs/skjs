import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Customer_skip_id_, CustomerStored, Customer } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each customer entry, emit the entry unchanged when the entry's value's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterCustomerByOwnerMapper implements Mapper<
  Customer_skip_id_,
  CustomerStored,
  Customer_skip_id_,
  CustomerStored
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Customer_skip_id_,
    values: Values<CustomerStored>,
    context: Context,
  ): Iterable<[Customer_skip_id_, CustomerStored]> {
    // > body
    const emits: [Customer_skip_id_, CustomerStored][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
