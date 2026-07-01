export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

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
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly costCents: number;
  readonly currency: string;
  readonly name: string;
  readonly nextRenewalDate: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type CreateSubscriptionRequest_skip_id_ = {
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly costCents: number;
  readonly currency: string;
  readonly name: string;
  readonly nextRenewalDate: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type CreateSubscriptionRequest_skip_value_ = {
  readonly billingCycle: BillingCycle;
  readonly category?: string;
  readonly costCents: number;
  readonly currency: string;
  readonly name: string;
  readonly nextRenewalDate: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type GetSpendingSummaryParams = { readonly userId: string };

export type GetSubscriptionParams = {
  readonly subscriptionId: string;
  readonly userId: string;
};

export type ListPaymentsByOwnerSubParams = {
  readonly subscriptionId: string;
  readonly userId: string;
};

export type ListSubscriptionsParams = {
  readonly dueBefore?: string;
  readonly status?: string;
  readonly userId: string;
};

export type PaymentEvent = {
  readonly amountCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly id: string;
  readonly method?: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt: string;
  readonly subscriptionId: string;
};

export type PaymentEventList = {
  readonly items: PaymentEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type PaymentEventList_skip_id_ = {
  readonly items: PaymentEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type PaymentEventList_skip_value_ = {
  readonly items: PaymentEvent[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type PaymentEvent_skip_id_ = string;

export type PaymentEvent_skip_value_ = {
  readonly amountCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly method?: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly paidAt: string;
  readonly subscriptionId: string;
};

export type PaymentKeyByPaidAt = {
  readonly id: string;
  readonly paidAt: string;
};

export type ReactivateSubscriptionRequest = {
  readonly nextRenewalDate?: string;
};

export type ReactivateSubscriptionRequest_skip_id_ = {
  readonly nextRenewalDate?: string;
};

export type ReactivateSubscriptionRequest_skip_value_ = {
  readonly nextRenewalDate?: string;
};

export type RecordPaymentRequest = {
  readonly amountCents: number;
  readonly currency: string;
  readonly method?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly paidAt?: string;
};

export type RecordPaymentRequest_skip_id_ = {
  readonly amountCents: number;
  readonly currency: string;
  readonly method?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly paidAt?: string;
};

export type RecordPaymentRequest_skip_value_ = {
  readonly amountCents: number;
  readonly currency: string;
  readonly method?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly paidAt?: string;
};

export type SpendingSummary = {
  readonly activeCount: number;
  readonly annualTotalCents: number;
  readonly cancelledCount: number;
  readonly currency?: string;
  readonly monthlyTotalCents: number;
};

export type SpendingSummary_skip_id_ = {
  readonly activeCount: number;
  readonly annualTotalCents: number;
  readonly cancelledCount: number;
  readonly currency?: string;
  readonly monthlyTotalCents: number;
};

export type SpendingSummary_skip_value_ = {
  readonly activeCount: number;
  readonly annualTotalCents: number;
  readonly cancelledCount: number;
  readonly currency?: string;
  readonly monthlyTotalCents: number;
};

export type SubKey = {
  readonly id: string;
  readonly name: string;
  readonly nextRenewalDate: string;
};

export type Subscription = {
  readonly billingCycle: BillingCycle;
  readonly cancelledAt?: string;
  readonly category?: string;
  readonly costCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly id: string;
  readonly name: string;
  readonly nextRenewalDate: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly provider?: string;
  readonly status: SubscriptionStatus;
  readonly updatedAt: string;
};

export type SubscriptionList = {
  readonly items: Subscription[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type SubscriptionList_skip_id_ = {
  readonly items: Subscription[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type SubscriptionList_skip_value_ = {
  readonly items: Subscription[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type SubscriptionStatus = "ACTIVE" | "CANCELLED";

export type SubscriptionStatus_skip_id_ = "ACTIVE" | "CANCELLED";

export type SubscriptionStatus_skip_value_ = "ACTIVE" | "CANCELLED";

export type Subscription_skip_id_ = string;

export type Subscription_skip_value_ = {
  readonly billingCycle: BillingCycle;
  readonly cancelledAt?: string;
  readonly category?: string;
  readonly costCents: number;
  readonly createdAt: string;
  readonly currency: string;
  readonly name: string;
  readonly nextRenewalDate: string;
  readonly notes?: string;
  readonly ownerId: string;
  readonly provider?: string;
  readonly status: SubscriptionStatus;
  readonly updatedAt: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateSubscriptionRequest = {
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly costCents?: number;
  readonly currency?: string;
  readonly name?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type UpdateSubscriptionRequest_skip_id_ = {
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly costCents?: number;
  readonly currency?: string;
  readonly name?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type UpdateSubscriptionRequest_skip_value_ = {
  readonly billingCycle?: BillingCycle;
  readonly category?: string;
  readonly costCents?: number;
  readonly currency?: string;
  readonly name?: string;
  readonly nextRenewalDate?: string;
  readonly notes?: string;
  readonly provider?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt: string;
};
