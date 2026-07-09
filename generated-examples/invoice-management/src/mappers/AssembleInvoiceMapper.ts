import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Invoice_skip_id_,
  InvoiceStored,
  Invoice_skip_value_,
  LineItem,
  InvoiceAmount,
  Invoice,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each invoice entry, consult lineItemsByInvoice for the LineItem values indexed by the entry's key (empty when the invoice has no line items yet); consult totalAmountByInvoice for the values indexed by the entry's key (default zero when no values are consulted); consult amountPaidByInvoice for the values indexed by the entry's key (default zero when no values are consulted). Sum the totalAmount contributions and round the sum to 2 decimals using half-away-from-zero rounding (i.e. multiply by 100, apply Math.round-style rounding where 0.5 rounds away from zero, divide by 100); sum the amountPaid contributions and round the sum to 2 decimals using the same half-away-from-zero rounding. Emit one output pair whose key is the entry's key and whose value lists every required field of Invoice_skip_value_ explicitly: ownerId sourced from the entry's value's ownerId field; customerId sourced from the entry's value's customerId field; invoiceNumber sourced from the entry's value's invoiceNumber field; status sourced from the entry's value's status field; currency sourced from the entry's value's currency field; createdAt sourced from the entry's value's createdAt field; totalAmount (readOnly, always present) sourced from the rounded sum of totalAmount contributions; amountPaid (readOnly, always present) sourced from the rounded sum of amountPaid contributions; balanceDue (readOnly, always present) computed as the rounded totalAmount minus the rounded amountPaid, then rounded to 2 decimals using the same half-away-from-zero rounding; lineItems (readOnly, always present) sourced from the consulted LineItem values (empty array when none). Optional fields: notes (present when the entry's value's notes field is present, sourced from the entry's value's notes field; absent otherwise); dueDate (present when the entry's value's dueDate field is present, sourced from the entry's value's dueDate field; absent otherwise); issuedAt (present when the entry's value's issuedAt field is present, sourced from the entry's value's issuedAt field; absent otherwise); paidAt (present when the entry's value's paidAt field is present, sourced from the entry's value's paidAt field; absent otherwise); voidedAt (present when the entry's value's voidedAt field is present, sourced from the entry's value's voidedAt field; absent otherwise).
export class AssembleInvoiceMapper implements Mapper<
  Invoice_skip_id_,
  InvoiceStored,
  Invoice_skip_id_,
  Invoice_skip_value_
> {
  constructor(
    private lineItemsByInvoice: EagerCollection<Invoice_skip_id_, LineItem>,
    private totalAmountByInvoice: EagerCollection<
      Invoice_skip_id_,
      InvoiceAmount
    >,
    private amountPaidByInvoice: EagerCollection<
      Invoice_skip_id_,
      InvoiceAmount
    >,
  ) {}

  mapEntry(
    key: Invoice_skip_id_,
    values: Values<InvoiceStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, Invoice_skip_value_]> {
    // > body
    const stored = values.toArray()[0];
    if (stored === undefined) return [];

    const lineItems = this.lineItemsByInvoice.getArray(key);
    const totalContributions = this.totalAmountByInvoice.getArray(key);
    const paidContributions = this.amountPaidByInvoice.getArray(key);

    const roundHalfAwayFromZero = (n: number): number => {
      const scaled = n * 100;
      const rounded =
        scaled >= 0 ? Math.floor(scaled + 0.5) : -Math.floor(-scaled + 0.5);
      return rounded / 100;
    };

    let totalRaw = 0;
    for (const v of totalContributions) totalRaw += v;
    let paidRaw = 0;
    for (const v of paidContributions) paidRaw += v;

    const totalAmount = roundHalfAwayFromZero(totalRaw);
    const amountPaid = roundHalfAwayFromZero(paidRaw);
    const balanceDue = roundHalfAwayFromZero(totalAmount - amountPaid);

    const out: Invoice_skip_value_ = {
      ownerId: stored.ownerId,
      customerId: stored.customerId,
      invoiceNumber: stored.invoiceNumber,
      status: stored.status,
      currency: stored.currency,
      createdAt: stored.createdAt,
      totalAmount,
      amountPaid,
      balanceDue,
      lineItems,
      ...(stored.notes !== undefined && { notes: stored.notes }),
      ...(stored.dueDate !== undefined && { dueDate: stored.dueDate }),
      ...(stored.issuedAt !== undefined && { issuedAt: stored.issuedAt }),
      ...(stored.paidAt !== undefined && { paidAt: stored.paidAt }),
      ...(stored.voidedAt !== undefined && { voidedAt: stored.voidedAt }),
    };

    return [[key, out]];
    // < body
  }
}
