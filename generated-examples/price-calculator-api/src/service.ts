import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  ProductId,
  ProductValue,
  PromotionId,
  PromotionValue,
  TaxRateId,
  TaxRateValue,
  ShippingRuleId,
  ShippingRuleValue,
  FinalPriceId,
  FinalPriceValue,
} from "./types.js";


export type Inputs = {
  products: InputDefinition<ProductId, ProductValue>;
  promotions: InputDefinition<PromotionId, PromotionValue>;
  taxRates: InputDefinition<TaxRateId, TaxRateValue>;
  shippingRules: InputDefinition<ShippingRuleId, ShippingRuleValue>;
};

export type InputCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  promotions: EagerCollection<PromotionId, PromotionValue>;
  taxRates: EagerCollection<TaxRateId, TaxRateValue>;
  shippingRules: EagerCollection<ShippingRuleId, ShippingRuleValue>;
};

export type GraphCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  promotions: EagerCollection<PromotionId, PromotionValue>;
  taxRates: EagerCollection<TaxRateId, TaxRateValue>;
  shippingRules: EagerCollection<ShippingRuleId, ShippingRuleValue>;
  promotionsByProduct: EagerCollection<ProductId, PromotionValue>;
  taxRatesByCategory: EagerCollection<string, TaxRateValue>;
  finalPrices: EagerCollection<FinalPriceId, FinalPriceValue>;
};

export type Resources = {
  readonly "products": ResourceClass<GraphCollections, {}>;
  readonly "promotions": ResourceClass<GraphCollections, {}>;
  readonly "taxRates": ResourceClass<GraphCollections, {}>;
  readonly "shippingRules": ResourceClass<GraphCollections, {}>;
  readonly "finalPrices": ResourceClass<GraphCollections, {}>;
};

export class PromotionsByProductMapper implements Mapper<PromotionId, PromotionValue, ProductId, PromotionValue> {
  constructor() {
  }

  mapEntry(
    _key: PromotionId,
    values: Values<PromotionValue>,
    _context: Context
  ): Iterable<[ProductId, PromotionValue]> {
    const result: Array<[ProductId, PromotionValue]> = Array.of();
    for (const v of values) {
      result.push([v.productId, v]);
    }
    return result;
  }
}

export class TaxRatesByCategoryMapper implements Mapper<TaxRateId, TaxRateValue, string, TaxRateValue> {
  constructor() {
  }

  mapEntry(
    _key: TaxRateId,
    values: Values<TaxRateValue>,
    _context: Context
  ): Iterable<[string, TaxRateValue]> {
    const result: Array<[string, TaxRateValue]> = Array.of();
    for (const v of values) {
      result.push([v.category, v]);
    }
    return result;
  }
}

export class ShippingRulesByWeightMapper implements Mapper<ShippingRuleId, ShippingRuleValue, string, ShippingRuleValue> {
  constructor() {
  }

  mapEntry(
    _key: ShippingRuleId,
    values: Values<ShippingRuleValue>,
    _context: Context
  ): Iterable<[string, ShippingRuleValue]> {
    const result: Array<[string, ShippingRuleValue]> = Array.of();
    for (const v of values) {
      result.push(["all", v]);
    }
    return result;
  }
}

export class FinalPriceMapper implements Mapper<ProductId, ProductValue, FinalPriceId, FinalPriceValue> {
  private promotionsByProduct: EagerCollection<ProductId, PromotionValue>;
  private taxRatesByCategory: EagerCollection<string, TaxRateValue>;
  private shippingRulesByWeight: EagerCollection<string, ShippingRuleValue>;

  constructor(
    promotionsByProduct: EagerCollection<ProductId, PromotionValue>,
    taxRatesByCategory: EagerCollection<string, TaxRateValue>,
    shippingRulesByWeight: EagerCollection<string, ShippingRuleValue>
  ) {
    this.promotionsByProduct = promotionsByProduct;
    this.taxRatesByCategory = taxRatesByCategory;
    this.shippingRulesByWeight = shippingRulesByWeight;
  }

  mapEntry(
    key: ProductId,
    values: Values<ProductValue>,
    _context: Context
  ): Iterable<[FinalPriceId, FinalPriceValue]> {
    const result: Array<[FinalPriceId, FinalPriceValue]> = Array.of();
    const currentTime = Date.now();

    for (const product of values) {
      const basePrice = product.basePrice;
      const productName = product.name;
      const category = product.category;
      const weight = product.weight;

      const promotions = this.promotionsByProduct.getArray(key);
      let discountAmount = 0;
      for (const promo of promotions) {
        if (promo.validFrom <= currentTime && currentTime <= promo.validUntil) {
          if (promo.discountType === "percentage") {
            discountAmount = discountAmount + (basePrice * promo.discountValue / 100);
          } else {
            discountAmount = discountAmount + promo.discountValue;
          }
        }
      }

      const priceAfterDiscount = basePrice - discountAmount;

      const taxRates = this.taxRatesByCategory.getArray(category);
      let taxAmount = 0;
      for (const taxRate of taxRates) {
        taxAmount = taxAmount + (priceAfterDiscount * taxRate.rate / 100);
      }

      let shippingCost = 0;
      const allShippingRules = this.shippingRulesByWeight.getArray("all");
      for (const rule of allShippingRules) {
        if (rule.minWeight <= weight && weight <= rule.maxWeight) {
          shippingCost = rule.baseCost + (weight * rule.costPerGram);
          break;
        }
      }

      const finalPrice = priceAfterDiscount + taxAmount + shippingCost;

      const finalPriceValue: FinalPriceValue = {
        productId: key,
        productName: productName,
        basePrice: basePrice,
        discountAmount: discountAmount,
        priceAfterDiscount: priceAfterDiscount,
        taxAmount: taxAmount,
        shippingCost: shippingCost,
        finalPrice: finalPrice
      };

      const finalPriceId: FinalPriceId = key;
      result.push([finalPriceId, finalPriceValue]);
    }
    return result;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products;
  }
}

export class PromotionsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PromotionId, PromotionValue> {
    return cs.promotions;
  }
}

export class TaxRatesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TaxRateId, TaxRateValue> {
    return cs.taxRates;
  }
}

export class ShippingRulesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ShippingRuleId, ShippingRuleValue> {
    return cs.shippingRules;
  }
}

export class FinalPricesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<FinalPriceId, FinalPriceValue> {
    return cs.finalPrices;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                    this.inputs = { products: new InputDefinition<ProductId, ProductValue>([]), promotions: new InputDefinition<PromotionId, PromotionValue>([]), taxRates: new InputDefinition<TaxRateId, TaxRateValue>([]), shippingRules: new InputDefinition<ShippingRuleId, ShippingRuleValue>([]) };
    this.resources = { "products": ProductsResource, "promotions": PromotionsResource, "taxRates": TaxRatesResource, "shippingRules": ShippingRulesResource, "finalPrices": FinalPricesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const promotionsByProduct = inputs.promotions.map(PromotionsByProductMapper);
    const taxRatesByCategory = inputs.taxRates.map(TaxRatesByCategoryMapper);
    const shippingRulesByWeight = inputs.shippingRules.map(ShippingRulesByWeightMapper);
    const finalPrices = inputs.products.map(FinalPriceMapper, promotionsByProduct, taxRatesByCategory, shippingRulesByWeight);

    return {
      products: inputs.products,
      promotions: inputs.promotions,
      taxRates: inputs.taxRates,
      shippingRules: inputs.shippingRules,
      promotionsByProduct: promotionsByProduct,
      taxRatesByCategory: taxRatesByCategory,
      finalPrices: finalPrices
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
