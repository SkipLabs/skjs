export type ApiError = { readonly code?: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
};

export type CartItemInput = {
  readonly name?: string;
  readonly quantity: number;
  readonly sku: string;
  readonly unitPrice: number;
  readonly unitWeightKg?: number;
};

export type CartItemInput_skip_id_ = {
  readonly name?: string;
  readonly quantity: number;
  readonly sku: string;
  readonly unitPrice: number;
  readonly unitWeightKg?: number;
};

export type CartItemInput_skip_value_ = {
  readonly name?: string;
  readonly quantity: number;
  readonly sku: string;
  readonly unitPrice: number;
  readonly unitWeightKg?: number;
};

export type CreatePromotionRequest = {
  readonly active: boolean;
  readonly code: string;
  readonly description?: string;
  readonly kind: PromotionKind;
  readonly minSubtotal?: number;
  readonly value: number;
};

export type CreatePromotionRequest_skip_id_ = {
  readonly active: boolean;
  readonly code: string;
  readonly description?: string;
  readonly kind: PromotionKind;
  readonly minSubtotal?: number;
  readonly value: number;
};

export type CreatePromotionRequest_skip_value_ = {
  readonly active: boolean;
  readonly code: string;
  readonly description?: string;
  readonly kind: PromotionKind;
  readonly minSubtotal?: number;
  readonly value: number;
};

export type CreateQuoteRequest = {
  readonly items: CartItemInput[];
  readonly promotionCode?: string;
  readonly shippingOptionId: string;
  readonly taxRateId: string;
};

export type CreateQuoteRequest_skip_id_ = {
  readonly items: CartItemInput[];
  readonly promotionCode?: string;
  readonly shippingOptionId: string;
  readonly taxRateId: string;
};

export type CreateQuoteRequest_skip_value_ = {
  readonly items: CartItemInput[];
  readonly promotionCode?: string;
  readonly shippingOptionId: string;
  readonly taxRateId: string;
};

export type CreateShippingOptionRequest = {
  readonly flatFee: number;
  readonly freeAboveSubtotal?: number;
  readonly name: string;
  readonly perKgFee?: number;
};

export type CreateShippingOptionRequest_skip_id_ = {
  readonly flatFee: number;
  readonly freeAboveSubtotal?: number;
  readonly name: string;
  readonly perKgFee?: number;
};

export type CreateShippingOptionRequest_skip_value_ = {
  readonly flatFee: number;
  readonly freeAboveSubtotal?: number;
  readonly name: string;
  readonly perKgFee?: number;
};

export type CreateTaxRateRequest = {
  readonly description?: string;
  readonly ratePercent: number;
  readonly region: string;
};

export type CreateTaxRateRequest_skip_id_ = {
  readonly description?: string;
  readonly ratePercent: number;
  readonly region: string;
};

export type CreateTaxRateRequest_skip_value_ = {
  readonly description?: string;
  readonly ratePercent: number;
  readonly region: string;
};

export type GetQuoteLineItemsByQuoteParams = { readonly quoteId: string };

export type ListPromotionsParams = { readonly active?: boolean };

export type ListTaxRatesParams = { readonly region?: string };

export type Promotion = {
  readonly active: boolean;
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly kind: PromotionKind;
  readonly minSubtotal?: number;
  readonly value: number;
};

export type PromotionKind = "PERCENT" | "FIXED";

export type PromotionKind_skip_id_ = "PERCENT" | "FIXED";

export type PromotionKind_skip_value_ = "PERCENT" | "FIXED";

export type PromotionList = { readonly items: Promotion[] };

export type PromotionList_skip_id_ = { readonly items: Promotion[] };

export type PromotionList_skip_value_ = { readonly items: Promotion[] };

export type Promotion_skip_id_ = string;

export type Promotion_skip_value_ = {
  readonly active: boolean;
  readonly code: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly kind: PromotionKind;
  readonly minSubtotal?: number;
  readonly value: number;
};

export type Quote = {
  readonly appliedPromotionId?: string;
  readonly createdAt: string;
  readonly discountAmount: number;
  readonly discountedSubtotal: number;
  readonly id: string;
  readonly lineItems: QuoteLineItem[];
  readonly promotionCode?: string;
  readonly shippingAmount: number;
  readonly shippingOptionId: string;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly taxRateId: string;
  readonly taxableBase: number;
  readonly total: number;
  readonly totalWeightKg: number;
};

export type QuoteLineItem = {
  readonly lineIndex: number;
  readonly lineTotal: number;
  readonly name?: string;
  readonly quantity: number;
  readonly quoteId: string;
  readonly sku: string;
  readonly unitPrice: number;
  readonly unitWeightKg?: number;
};

export type QuoteLineItemKey = {
  readonly lineIndex: number;
  readonly quoteId: string;
};

export type QuoteLineItem_skip_id_ = {
  readonly lineIndex: number;
  readonly quoteId: string;
};

export type QuoteLineItem_skip_value_ = {
  readonly lineTotal: number;
  readonly name?: string;
  readonly quantity: number;
  readonly sku: string;
  readonly unitPrice: number;
  readonly unitWeightKg?: number;
};

export type QuoteList = { readonly items: Quote[] };

export type QuoteList_skip_id_ = { readonly items: Quote[] };

export type QuoteList_skip_value_ = { readonly items: Quote[] };

export type QuoteStored = {
  readonly appliedPromotionId?: string;
  readonly createdAt: string;
  readonly discountAmount: number;
  readonly discountedSubtotal: number;
  readonly promotionCode?: string;
  readonly shippingAmount: number;
  readonly shippingOptionId: string;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly taxRateId: string;
  readonly taxableBase: number;
  readonly total: number;
  readonly totalWeightKg: number;
};

export type Quote_skip_id_ = string;

export type Quote_skip_value_ = {
  readonly appliedPromotionId?: string;
  readonly createdAt: string;
  readonly discountAmount: number;
  readonly discountedSubtotal: number;
  readonly lineItems: QuoteLineItem[];
  readonly promotionCode?: string;
  readonly shippingAmount: number;
  readonly shippingOptionId: string;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly taxRateId: string;
  readonly taxableBase: number;
  readonly total: number;
  readonly totalWeightKg: number;
};

export type ShippingOption = {
  readonly createdAt: string;
  readonly flatFee: number;
  readonly freeAboveSubtotal?: number;
  readonly id: string;
  readonly name: string;
  readonly perKgFee?: number;
};

export type ShippingOptionList = { readonly items: ShippingOption[] };

export type ShippingOptionList_skip_id_ = { readonly items: ShippingOption[] };

export type ShippingOptionList_skip_value_ = {
  readonly items: ShippingOption[];
};

export type ShippingOption_skip_id_ = string;

export type ShippingOption_skip_value_ = {
  readonly createdAt: string;
  readonly flatFee: number;
  readonly freeAboveSubtotal?: number;
  readonly name: string;
  readonly perKgFee?: number;
};

export type TaxRate = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly ratePercent: number;
  readonly region: string;
};

export type TaxRateList = { readonly items: TaxRate[] };

export type TaxRateList_skip_id_ = { readonly items: TaxRate[] };

export type TaxRateList_skip_value_ = { readonly items: TaxRate[] };

export type TaxRate_skip_id_ = string;

export type TaxRate_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly ratePercent: number;
  readonly region: string;
};

export type UpdatePromotionRequest = {
  readonly active?: boolean;
  readonly code?: string;
  readonly description?: string;
  readonly kind?: PromotionKind;
  readonly minSubtotal?: number;
  readonly value?: number;
};

export type UpdatePromotionRequest_skip_id_ = {
  readonly active?: boolean;
  readonly code?: string;
  readonly description?: string;
  readonly kind?: PromotionKind;
  readonly minSubtotal?: number;
  readonly value?: number;
};

export type UpdatePromotionRequest_skip_value_ = {
  readonly active?: boolean;
  readonly code?: string;
  readonly description?: string;
  readonly kind?: PromotionKind;
  readonly minSubtotal?: number;
  readonly value?: number;
};

export type UpdateShippingOptionRequest = {
  readonly flatFee?: number;
  readonly freeAboveSubtotal?: number;
  readonly name?: string;
  readonly perKgFee?: number;
};

export type UpdateShippingOptionRequest_skip_id_ = {
  readonly flatFee?: number;
  readonly freeAboveSubtotal?: number;
  readonly name?: string;
  readonly perKgFee?: number;
};

export type UpdateShippingOptionRequest_skip_value_ = {
  readonly flatFee?: number;
  readonly freeAboveSubtotal?: number;
  readonly name?: string;
  readonly perKgFee?: number;
};

export type UpdateTaxRateRequest = {
  readonly description?: string;
  readonly ratePercent?: number;
  readonly region?: string;
};

export type UpdateTaxRateRequest_skip_id_ = {
  readonly description?: string;
  readonly ratePercent?: number;
  readonly region?: string;
};

export type UpdateTaxRateRequest_skip_value_ = {
  readonly description?: string;
  readonly ratePercent?: number;
  readonly region?: string;
};
