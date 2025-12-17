export type PercentageFixedEnum = "percentage" | "fixed";

export type ProductId = string;

export type ProductValue = {
  name: string;
  basePrice: number;
  category: string;
  weight: number;
};

export type Product = ProductValue & { id: ProductId };

export type PromotionId = string;

export type PromotionValue = {
  productId: string;
  discountType: PercentageFixedEnum;
  discountValue: number;
  validFrom: number;
  validUntil: number;
};

export type Promotion = PromotionValue & { id: PromotionId };

export type TaxRateId = string;

export type TaxRateValue = {
  category: string;
  rate: number;
};

export type TaxRate = TaxRateValue & { id: TaxRateId };

export type ShippingRuleId = string;

export type ShippingRuleValue = {
  minWeight: number;
  maxWeight: number;
  baseCost: number;
  costPerGram: number;
};

export type ShippingRule = ShippingRuleValue & { id: ShippingRuleId };

export type FinalPriceId = string;

export type FinalPriceValue = {
  productId: string;
  productName: string;
  basePrice: number;
  discountAmount: number;
  priceAfterDiscount: number;
  taxAmount: number;
  shippingCost: number;
  finalPrice: number;
};

export type FinalPrice = FinalPriceValue & { id: FinalPriceId };
