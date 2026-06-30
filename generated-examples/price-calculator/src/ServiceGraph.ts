import type {
  Promotion_skip_id_,
  Promotion,
  Promotion_skip_value_,
  QuoteLineItemKey,
  QuoteLineItem_skip_value_,
  QuoteLineItem,
  Quote_skip_id_,
  Quote,
  QuoteStored,
  ShippingOption_skip_id_,
  ShippingOption,
  ShippingOption_skip_value_,
  TaxRate_skip_id_,
  TaxRate,
  TaxRate_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly quoteLineItems: EagerCollection<
    QuoteLineItemKey,
    QuoteLineItem_skip_value_
  >;
  readonly quotes: EagerCollection<Quote_skip_id_, QuoteStored>;
  readonly shippingOptions: EagerCollection<
    ShippingOption_skip_id_,
    ShippingOption_skip_value_
  >;
  readonly taxRates: EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly quoteLineItems: EagerCollection<
    QuoteLineItemKey,
    QuoteLineItem_skip_value_
  >;
  readonly quotes: EagerCollection<Quote_skip_id_, QuoteStored>;
  readonly shippingOptions: EagerCollection<
    ShippingOption_skip_id_,
    ShippingOption_skip_value_
  >;
  readonly taxRates: EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_promotions = inputs.promotions;
  const output_quoteLineItems = inputs.quoteLineItems;
  const output_quotes = inputs.quotes;
  const output_shippingOptions = inputs.shippingOptions;
  const output_taxRates = inputs.taxRates;
  return {
    promotions: output_promotions,
    quoteLineItems: output_quoteLineItems,
    quotes: output_quotes,
    shippingOptions: output_shippingOptions,
    taxRates: output_taxRates,
  };
}
