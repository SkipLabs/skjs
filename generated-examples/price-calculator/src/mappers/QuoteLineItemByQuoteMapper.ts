import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  QuoteLineItemKey,
  QuoteLineItem_skip_value_,
  Quote_skip_id_,
  QuoteLineItem,
  Quote,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit one output pair whose key is sourced from the entry's key's quoteId field. The output value lists every required field of QuoteLineItem explicitly: quoteId sourced from the entry's key's quoteId field (re-injected since it is no longer part of the new key); lineIndex sourced from the entry's key's lineIndex field (re-injected since it is no longer part of the new key); sku sourced from the entry's value's sku field; unitPrice sourced from the entry's value's unitPrice field; quantity sourced from the entry's value's quantity field; lineTotal sourced from the entry's value's lineTotal field. Optional fields: name is present when the entry's value's name field is present, sourced from the entry's value's name field; absent otherwise. unitWeightKg is present when the entry's value's unitWeightKg field is present, sourced from the entry's value's unitWeightKg field; absent otherwise.
export class QuoteLineItemByQuoteMapper implements Mapper<
  QuoteLineItemKey,
  QuoteLineItem_skip_value_,
  Quote_skip_id_,
  QuoteLineItem
> {
  mapEntry(
    key: QuoteLineItemKey,
    values: Values<QuoteLineItem_skip_value_>,
    context: Context,
  ): Iterable<[Quote_skip_id_, QuoteLineItem]> {
    // > body
    const emits: [Quote_skip_id_, QuoteLineItem][] = [];
    for (const value of values.toArray()) {
      const item: QuoteLineItem = {
        quoteId: key.quoteId,
        lineIndex: key.lineIndex,
        sku: value.sku,
        unitPrice: value.unitPrice,
        quantity: value.quantity,
        lineTotal: value.lineTotal,
        ...(value.name !== undefined && { name: value.name }),
        ...(value.unitWeightKg !== undefined && {
          unitWeightKg: value.unitWeightKg,
        }),
      };
      emits.push([key.quoteId, item]);
    }
    return emits;
    // < body
  }
}
