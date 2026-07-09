import type { Json } from "@skipruntime/core";

export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type AppliedPromotion = {
  readonly discountApplied: number;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly promotionId: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type AppliedPromotion_skip_id_ = {
  readonly discountApplied: number;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly promotionId: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type AppliedPromotion_skip_value_ = {
  readonly discountApplied: number;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly promotionId: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type AppliedTax = {
  readonly ratePercent: number;
  readonly region: string;
  readonly taxApplied: number;
  readonly taxRuleId: string;
} & { readonly [key: string]: Json | null };

export type AppliedTax_skip_id_ = {
  readonly ratePercent: number;
  readonly region: string;
  readonly taxApplied: number;
  readonly taxRuleId: string;
} & { readonly [key: string]: Json | null };

export type AppliedTax_skip_value_ = {
  readonly ratePercent: number;
  readonly region: string;
  readonly taxApplied: number;
  readonly taxRuleId: string;
} & { readonly [key: string]: Json | null };

export type CalculatePriceRequest = {
  readonly basePrice: number;
  readonly promotionIds?: string[];
  readonly quantity?: number;
  readonly shipping?: number;
  readonly taxRuleIds?: string[];
} & { readonly [key: string]: Json | null };

export type CalculatePriceRequest_skip_id_ = {
  readonly basePrice: number;
  readonly promotionIds?: string[];
  readonly quantity?: number;
  readonly shipping?: number;
  readonly taxRuleIds?: string[];
} & { readonly [key: string]: Json | null };

export type CalculatePriceRequest_skip_value_ = {
  readonly basePrice: number;
  readonly promotionIds?: string[];
  readonly quantity?: number;
  readonly shipping?: number;
  readonly taxRuleIds?: string[];
} & { readonly [key: string]: Json | null };

export type CreatePromotionRequest = {
  readonly active?: boolean;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type CreatePromotionRequest_skip_id_ = {
  readonly active?: boolean;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type CreatePromotionRequest_skip_value_ = {
  readonly active?: boolean;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type CreateTaxRuleRequest = {
  readonly ratePercent: number;
  readonly region: string;
} & { readonly [key: string]: Json | null };

export type CreateTaxRuleRequest_skip_id_ = {
  readonly ratePercent: number;
  readonly region: string;
} & { readonly [key: string]: Json | null };

export type CreateTaxRuleRequest_skip_value_ = {
  readonly ratePercent: number;
  readonly region: string;
} & { readonly [key: string]: Json | null };

export type GetPromotionParams = { readonly promotionId: string } & {
  readonly [key: string]: Json | null;
};

export type GetTaxRuleParams = { readonly taxRuleId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPromotionsParams = { readonly activeOnly?: boolean } & {
  readonly [key: string]: Json | null;
};

export type ListTaxRulesParams = { readonly region?: string } & {
  readonly [key: string]: Json | null;
};

export type PriceBreakdown = {
  readonly appliedPromotions: AppliedPromotion[];
  readonly appliedTaxes: AppliedTax[];
  readonly discountedSubtotal: number;
  readonly shipping: number;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly total: number;
  readonly totalDiscount: number;
} & { readonly [key: string]: Json | null };

export type PriceBreakdown_skip_id_ = {
  readonly appliedPromotions: AppliedPromotion[];
  readonly appliedTaxes: AppliedTax[];
  readonly discountedSubtotal: number;
  readonly shipping: number;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly total: number;
  readonly totalDiscount: number;
} & { readonly [key: string]: Json | null };

export type PriceBreakdown_skip_value_ = {
  readonly appliedPromotions: AppliedPromotion[];
  readonly appliedTaxes: AppliedTax[];
  readonly discountedSubtotal: number;
  readonly shipping: number;
  readonly subtotal: number;
  readonly taxAmount: number;
  readonly total: number;
  readonly totalDiscount: number;
} & { readonly [key: string]: Json | null };

export type Promotion = {
  readonly active: boolean;
  readonly createdAt: string;
  readonly id: string;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type PromotionKind = "PERCENT" | "FIXED";

export type PromotionKind_skip_id_ = "PERCENT" | "FIXED";

export type PromotionKind_skip_value_ = "PERCENT" | "FIXED";

export type PromotionList = { readonly items: Promotion[] } & {
  readonly [key: string]: Json | null;
};

export type PromotionList_skip_id_ = { readonly items: Promotion[] } & {
  readonly [key: string]: Json | null;
};

export type PromotionList_skip_value_ = { readonly items: Promotion[] } & {
  readonly [key: string]: Json | null;
};

export type Promotion_skip_id_ = string;

export type Promotion_skip_value_ = {
  readonly active: boolean;
  readonly createdAt: string;
  readonly kind: PromotionKind;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
  readonly value: number;
} & { readonly [key: string]: Json | null };

export type TaxRule = {
  readonly createdAt: string;
  readonly id: string;
  readonly ownerId: string;
  readonly ratePercent: number;
  readonly region: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type TaxRuleList = { readonly items: TaxRule[] } & {
  readonly [key: string]: Json | null;
};

export type TaxRuleList_skip_id_ = { readonly items: TaxRule[] } & {
  readonly [key: string]: Json | null;
};

export type TaxRuleList_skip_value_ = { readonly items: TaxRule[] } & {
  readonly [key: string]: Json | null;
};

export type TaxRule_skip_id_ = string;

export type TaxRule_skip_value_ = {
  readonly createdAt: string;
  readonly ownerId: string;
  readonly ratePercent: number;
  readonly region: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdatePromotionRequest = {
  readonly active?: boolean;
  readonly kind?: PromotionKind;
  readonly name?: string;
  readonly value?: number;
} & { readonly [key: string]: Json | null };

export type UpdatePromotionRequest_skip_id_ = {
  readonly active?: boolean;
  readonly kind?: PromotionKind;
  readonly name?: string;
  readonly value?: number;
} & { readonly [key: string]: Json | null };

export type UpdatePromotionRequest_skip_value_ = {
  readonly active?: boolean;
  readonly kind?: PromotionKind;
  readonly name?: string;
  readonly value?: number;
} & { readonly [key: string]: Json | null };

export type UpdateTaxRuleRequest = {
  readonly ratePercent?: number;
  readonly region?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTaxRuleRequest_skip_id_ = {
  readonly ratePercent?: number;
  readonly region?: string;
} & { readonly [key: string]: Json | null };

export type UpdateTaxRuleRequest_skip_value_ = {
  readonly ratePercent?: number;
  readonly region?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
