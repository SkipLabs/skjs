import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Invoice_skip_id_,
  InvoiceStored,
  Invoice,
  LineItem,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each invoice entry, consult lineItemsByInvoice for the LineItem values indexed by the entry's key. Collect those values into an array. Compute subtotal as the sum of each value's lineTotal field across the consulted values (zero when no values are consulted). Emit one output pair whose key is the entry's key and whose value lists every required field of Invoice explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; customerId sourced from the entry's value's customerId field; invoiceNumber sourced from the entry's value's invoiceNumber field; status sourced from the entry's value's status field; currency sourced from the entry's value's currency field; createdAt sourced from the entry's value's createdAt field; subtotal as computed; total equal to the computed subtotal; lineItems set to the collected array (empty array when no values are consulted). Optional fields: notes is present when the entry's value's notes field is present, sourced from it; absent otherwise. dueDate is present when the entry's value's dueDate field is present, sourced from it; absent otherwise. sentAt is present when the entry's value's sentAt field is present, sourced from it; absent otherwise. paidAt is present when the entry's value's paidAt field is present, sourced from it; absent otherwise. voidedAt is present when the entry's value's voidedAt field is present, sourced from it; absent otherwise.
export class AssembleInvoiceMapper implements Mapper<
  Invoice_skip_id_,
  InvoiceStored,
  Invoice_skip_id_,
  Invoice
> {
  constructor(
    private lineItemsByInvoice: EagerCollection<Invoice_skip_id_, LineItem>,
  ) {}

  mapEntry(
    key: Invoice_skip_id_,
    values: Values<InvoiceStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, Invoice]> {
    // > body
    const emits: [Invoice_skip_id_, Invoice][] = [];
    for (const value of values.toArray()) {
      const lineItems = this.lineItemsByInvoice.getArray(key);
      let subtotal = 0;
      for (const li of lineItems) subtotal += li.lineTotal;
      const invoice: Invoice = {
        id: key,
        ownerId: value.ownerId,
        customerId: value.customerId,
        invoiceNumber: value.invoiceNumber,
        status: value.status,
        currency: value.currency,
        createdAt: value.createdAt,
        subtotal,
        total: subtotal,
        lineItems,
        ...(value.notes !== undefined && { notes: value.notes }),
        ...(value.dueDate !== undefined && { dueDate: value.dueDate }),
        ...(value.sentAt !== undefined && { sentAt: value.sentAt }),
        ...(value.paidAt !== undefined && { paidAt: value.paidAt }),
        ...(value.voidedAt !== undefined && { voidedAt: value.voidedAt }),
      };
      emits.push([key, invoice]);
    }
    return emits;
    // < body
  }
}
