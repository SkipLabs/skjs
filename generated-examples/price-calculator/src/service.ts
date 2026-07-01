import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPromotionResource } from "./resources/GetPromotionResource.js";
import { GetTaxRateResource } from "./resources/GetTaxRateResource.js";
import { ListPromotionsResource } from "./resources/ListPromotionsResource.js";
import { ListTaxRatesResource } from "./resources/ListTaxRatesResource.js";
import { QuoteLineItemsByQuoteResource } from "./resources/QuoteLineItemsByQuoteResource.js";
import { QuotesResource } from "./resources/QuotesResource.js";
import { ShippingOptionsResource } from "./resources/ShippingOptionsResource.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  QuoteLineItemKey,
  QuoteLineItem_skip_value_,
  Quote_skip_id_,
  QuoteStored,
  ShippingOption_skip_id_,
  ShippingOption_skip_value_,
  TaxRate_skip_id_,
  TaxRate_skip_value_,
  ListPromotionsParams,
  ListTaxRatesParams,
  GetQuoteLineItemsByQuoteParams,
  Promotion,
  QuoteLineItem,
  Quote,
  ShippingOption,
  TaxRate,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly promotions: InputDefinition<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly quoteLineItems: InputDefinition<
    QuoteLineItemKey,
    QuoteLineItem_skip_value_
  >;
  readonly quotes: InputDefinition<Quote_skip_id_, QuoteStored>;
  readonly shippingOptions: InputDefinition<
    ShippingOption_skip_id_,
    ShippingOption_skip_value_
  >;
  readonly taxRates: InputDefinition<TaxRate_skip_id_, TaxRate_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPromotionResource: ResourceClass<GraphCollections, Json>;
  readonly getTaxRateResource: ResourceClass<GraphCollections, Json>;
  readonly listPromotionsResource: ResourceClass<
    GraphCollections,
    ListPromotionsParams
  >;
  readonly listTaxRatesResource: ResourceClass<
    GraphCollections,
    ListTaxRatesParams
  >;
  readonly quoteLineItemsByQuoteResource: ResourceClass<
    GraphCollections,
    GetQuoteLineItemsByQuoteParams
  >;
  readonly quotesResource: ResourceClass<GraphCollections, Json>;
  readonly shippingOptionsResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      promotions: new InputDefinition<
        Promotion_skip_id_,
        Promotion_skip_value_
      >([]),
      quoteLineItems: new InputDefinition<
        QuoteLineItemKey,
        QuoteLineItem_skip_value_
      >([]),
      quotes: new InputDefinition<Quote_skip_id_, QuoteStored>([]),
      shippingOptions: new InputDefinition<
        ShippingOption_skip_id_,
        ShippingOption_skip_value_
      >([]),
      taxRates: new InputDefinition<TaxRate_skip_id_, TaxRate_skip_value_>([]),
    };
    this.resources = {
      getPromotionResource: GetPromotionResource,
      getTaxRateResource: GetTaxRateResource,
      listPromotionsResource: ListPromotionsResource,
      listTaxRatesResource: ListTaxRatesResource,
      quoteLineItemsByQuoteResource: QuoteLineItemsByQuoteResource,
      quotesResource: QuotesResource,
      shippingOptionsResource: ShippingOptionsResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
