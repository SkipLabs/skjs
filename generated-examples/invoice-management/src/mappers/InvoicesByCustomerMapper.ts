import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Invoice_skip_id_,
  InvoiceStored,
  Customer_skip_id_,
  Invoice,
  Customer,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each invoice entry, emit one output pair whose key is sourced from the entry's value's customerId field and whose value is the entry's value unchanged. The original invoice id from the entry's key is dropped because the consumer (deleteCustomer's cascade blocker check) only needs to know whether ANY invoice exists for a given customerId — per-row id reconstruction is not needed here.
export class InvoicesByCustomerMapper implements Mapper<
  Invoice_skip_id_,
  InvoiceStored,
  Customer_skip_id_,
  InvoiceStored
> {
  mapEntry(
    key: Invoice_skip_id_,
    values: Values<InvoiceStored>,
    context: Context,
  ): Iterable<[Customer_skip_id_, InvoiceStored]> {
    // > body
    const emits: [Customer_skip_id_, InvoiceStored][] = [];
    for (const value of values.toArray()) {
      emits.push([value.customerId, value]);
    }
    return emits;
    // < body
  }
}
