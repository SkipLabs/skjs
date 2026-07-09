import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type BillingCycle = "WEEKLY" | "MONTHLY" | "QUARTERLY" | "YEARLY";

export type BillingCycle_skip_id_ =
  | "WEEKLY"
  | "MONTHLY"
  | "QUARTERLY"
  | "YEARLY";

export type BillingCycle_skip_value_ =
  | "WEEKLY"
  | "MONTHLY"
  | "QUARTERLY"
  | "YEARLY";

export type CreateSubscriptionRequest = {
  readonly amount: number;
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly currency: Currency;
  readonly name: string;
  readonly notes?: string;
  readonly startDate: string;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type CreateSubscriptionRequest_skip_id_ = {
  readonly amount: number;
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly currency: Currency;
  readonly name: string;
  readonly notes?: string;
  readonly startDate: string;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type CreateSubscriptionRequest_skip_value_ = {
  readonly amount: number;
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly currency: Currency;
  readonly name: string;
  readonly notes?: string;
  readonly startDate: string;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type Currency = string;

export type Currency_skip_id_ = string;

export type Currency_skip_value_ = string;

export type GetSubscriptionParams = { readonly subscriptionId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPaymentsParams = { readonly subscriptionId: string } & {
  readonly [key: string]: Json | null;
};

export type ListSubscriptionsParams = {
  readonly status?: SubscriptionStatus;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Payment = {
  readonly amount: number;
  readonly createdAt: string;
  readonly currency: Currency;
  readonly id: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly paidAt: string;
  readonly subscriptionId: string;
} & { readonly [key: string]: Json | null };

export type PaymentPage = {
  readonly items: Payment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PaymentPage_skip_id_ = {
  readonly items: Payment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type PaymentPage_skip_value_ = {
  readonly items: Payment[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Payment_skip_id_ = string;

export type Payment_skip_value_ = {
  readonly amount: number;
  readonly createdAt: string;
  readonly currency: Currency;
  readonly note?: string;
  readonly ownerId: string;
  readonly paidAt: string;
  readonly subscriptionId: string;
} & { readonly [key: string]: Json | null };

export type RecordPaymentRequest = {
  readonly amount?: number;
  readonly currency?: Currency;
  readonly note?: string;
  readonly paidAt?: string;
} & { readonly [key: string]: Json | null };

export type RecordPaymentRequest_skip_id_ = {
  readonly amount?: number;
  readonly currency?: Currency;
  readonly note?: string;
  readonly paidAt?: string;
} & { readonly [key: string]: Json | null };

export type RecordPaymentRequest_skip_value_ = {
  readonly amount?: number;
  readonly currency?: Currency;
  readonly note?: string;
  readonly paidAt?: string;
} & { readonly [key: string]: Json | null };

export type SpendingSummary = {
  readonly activeCount: number;
  readonly currency: Currency;
  readonly monthlyTotal: number;
  readonly ownerId: string;
  readonly totalSubscriptionCount: number;
  readonly yearlyTotal: number;
} & { readonly [key: string]: Json | null };

export type SpendingSummaryParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type SpendingSummary_skip_id_ = {
  readonly activeCount: number;
  readonly currency: Currency;
  readonly monthlyTotal: number;
  readonly ownerId: string;
  readonly totalSubscriptionCount: number;
  readonly yearlyTotal: number;
} & { readonly [key: string]: Json | null };

export type SpendingSummary_skip_value_ = {
  readonly activeCount: number;
  readonly currency: Currency;
  readonly monthlyTotal: number;
  readonly ownerId: string;
  readonly totalSubscriptionCount: number;
  readonly yearlyTotal: number;
} & { readonly [key: string]: Json | null };

export type Subscription = {
  readonly amount: number;
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly createdAt: string;
  readonly currency: Currency;
  readonly id: string;
  readonly name: string;
  readonly nextRenewalAt: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly startDate: string;
  readonly status: SubscriptionStatus;
  readonly updatedAt: string;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type SubscriptionPage = {
  readonly items: Subscription[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubscriptionPage_skip_id_ = {
  readonly items: Subscription[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubscriptionPage_skip_value_ = {
  readonly items: Subscription[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type SubscriptionStatus = "ACTIVE" | "PAUSED" | "CANCELLED";

export type SubscriptionStatus_skip_id_ = "ACTIVE" | "PAUSED" | "CANCELLED";

export type SubscriptionStatus_skip_value_ = "ACTIVE" | "PAUSED" | "CANCELLED";

export type Subscription_skip_id_ = string;

export type Subscription_skip_value_ = {
  readonly amount: number;
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly createdAt: string;
  readonly currency: Currency;
  readonly name: string;
  readonly nextRenewalAt: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly startDate: string;
  readonly status: SubscriptionStatus;
  readonly updatedAt: string;
  readonly vendor?: string;
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

export type UpdateSubscriptionRequest = {
  readonly amount?: number;
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly currency?: Currency;
  readonly name?: string;
  readonly notes?: string;
  readonly startDate?: string;
  readonly status?: SubscriptionStatus;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSubscriptionRequest_skip_id_ = {
  readonly amount?: number;
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly currency?: Currency;
  readonly name?: string;
  readonly notes?: string;
  readonly startDate?: string;
  readonly status?: SubscriptionStatus;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type UpdateSubscriptionRequest_skip_value_ = {
  readonly amount?: number;
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly currency?: Currency;
  readonly name?: string;
  readonly notes?: string;
  readonly startDate?: string;
  readonly status?: SubscriptionStatus;
  readonly vendor?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
