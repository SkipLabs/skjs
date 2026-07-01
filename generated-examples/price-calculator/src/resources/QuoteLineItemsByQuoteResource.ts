import { FilterQuoteLineItemByQuoteParamMapper } from "../mappers/FilterQuoteLineItemByQuoteParamMapper.js";
import { QuoteLineItemByQuoteMapper } from "../mappers/QuoteLineItemByQuoteMapper.js";
import type {
  QuoteLineItemKey,
  QuoteLineItem_skip_value_,
  Quote_skip_id_,
  QuoteLineItem,
  GetQuoteLineItemsByQuoteParams,
  Quote,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface QuoteLineItemsByQuoteResourceInputs extends SharedCollections {
  readonly quoteLineItems: EagerCollection<
    QuoteLineItemKey,
    QuoteLineItem_skip_value_
  >;
}

export class QuoteLineItemsByQuoteResource implements Resource<QuoteLineItemsByQuoteResourceInputs> {
  private readonly quoteId: string;

  constructor(params: GetQuoteLineItemsByQuoteParams) {
    this.quoteId = params.quoteId;
  }

  instantiate(
    inputs: QuoteLineItemsByQuoteResourceInputs,
    _context: Context,
  ): EagerCollection<Quote_skip_id_, QuoteLineItem> {
    const byQuote = inputs.quoteLineItems.map(QuoteLineItemByQuoteMapper);
    return byQuote.map(FilterQuoteLineItemByQuoteParamMapper, this.quoteId);
  }
}
