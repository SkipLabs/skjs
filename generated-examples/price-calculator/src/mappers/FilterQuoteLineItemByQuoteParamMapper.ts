import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Quote_skip_id_, QuoteLineItem, Quote } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the quoteId key: when the entry's key does not equal the quoteId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output pair under the entry's key paired with the value. (The input collection accumulates every line item belonging to the same quote under one key — singleton-only access would raise on any quote with two or more line items. The upstream re-key by QuoteLineItemByQuoteMapper collapses the composite QuoteLineItemKey to the parent Quote id, so iteration over the values list is required.)
export class FilterQuoteLineItemByQuoteParamMapper implements Mapper<
  Quote_skip_id_,
  QuoteLineItem,
  Quote_skip_id_,
  QuoteLineItem
> {
  constructor(private quoteId: string) {}

  mapEntry(
    key: Quote_skip_id_,
    values: Values<QuoteLineItem>,
    context: Context,
  ): Iterable<[Quote_skip_id_, QuoteLineItem]> {
    // > body
    if (key !== this.quoteId) return [];
    const emits: [Quote_skip_id_, QuoteLineItem][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
