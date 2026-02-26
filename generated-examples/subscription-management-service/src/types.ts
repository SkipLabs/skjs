export type ActiveCancelledExpiredEnum = "active" | "cancelled" | "expired";

export type CustomerId = string;

export type CustomerValue = {
  email: string;
  name: string;
  createdAt: number;
};

export type Customer = CustomerValue & { id: CustomerId };

export type PlanId = string;

export type PlanValue = {
  name: string;
  price: number;
  billingPeriodDays: number;
  features: string;
};

export type Plan = PlanValue & { id: PlanId };

export type SubscriptionId = string;

export type SubscriptionValue = {
  customerId: string;
  planId: string;
  status: ActiveCancelledExpiredEnum;
  startDate: number;
  endDate: number;
  autoRenew: number;
};

export type Subscription = SubscriptionValue & { id: SubscriptionId };

export type SubscriptionsByCustomerResourceParams = {
  customerId: string;
};
