import type { Json } from "@skipruntime/core";

export type Algorithm = "SLIDING_WINDOW" | "FIXED_WINDOW" | "TOKEN_BUCKET";

export type Algorithm_skip_id_ =
  | "SLIDING_WINDOW"
  | "FIXED_WINDOW"
  | "TOKEN_BUCKET";

export type Algorithm_skip_value_ =
  | "SLIDING_WINDOW"
  | "FIXED_WINDOW"
  | "TOKEN_BUCKET";

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

export type CheckRequest = { readonly cost: number; readonly key: string } & {
  readonly [key: string]: Json | null;
};

export type CheckRequest_skip_id_ = {
  readonly cost: number;
  readonly key: string;
} & { readonly [key: string]: Json | null };

export type CheckRequest_skip_value_ = {
  readonly cost: number;
  readonly key: string;
} & { readonly [key: string]: Json | null };

export type CheckResult = {
  readonly allowed: boolean;
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly retryAfterMs?: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type CheckResult_skip_id_ = {
  readonly allowed: boolean;
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly retryAfterMs?: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type CheckResult_skip_value_ = {
  readonly allowed: boolean;
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly retryAfterMs?: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type ConsumptionEvent = {
  readonly cost: number;
  readonly id: string;
  readonly key: string;
  readonly occurredAtMs: number;
  readonly policyId: string;
} & { readonly [key: string]: Json | null };

export type ConsumptionEvent_skip_id_ = string;

export type ConsumptionEvent_skip_value_ = {
  readonly cost: number;
  readonly key: string;
  readonly occurredAtMs: number;
  readonly policyId: string;
} & { readonly [key: string]: Json | null };

export type CreatePolicyRequest = {
  readonly algorithm: Algorithm;
  readonly description?: string;
  readonly limit: number;
  readonly name: string;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type CreatePolicyRequest_skip_id_ = {
  readonly algorithm: Algorithm;
  readonly description?: string;
  readonly limit: number;
  readonly name: string;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type CreatePolicyRequest_skip_value_ = {
  readonly algorithm: Algorithm;
  readonly description?: string;
  readonly limit: number;
  readonly name: string;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type GetPolicyParams = { readonly policyId: string } & {
  readonly [key: string]: Json | null;
};

export type KeyStatus = {
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type KeyStatus_skip_id_ = {
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type KeyStatus_skip_value_ = {
  readonly key: string;
  readonly limit: number;
  readonly nowMs: number;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAtMs: number;
  readonly used: number;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type ListConsumptionEventsParams = { readonly policyId: string } & {
  readonly [key: string]: Json | null;
};

export type ListPoliciesParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Policy = {
  readonly algorithm: Algorithm;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly limit: number;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly windowSeconds: number;
} & { readonly [key: string]: Json | null };

export type Policy_skip_id_ = string;

export type Policy_skip_value_ = {
  readonly algorithm: Algorithm;
  readonly createdAt: string;
  readonly description?: string;
  readonly limit: number;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
  readonly windowSeconds: number;
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

export type UpdatePolicyRequest = {
  readonly algorithm?: Algorithm;
  readonly description?: string;
  readonly limit?: number;
  readonly name?: string;
  readonly windowSeconds?: number;
} & { readonly [key: string]: Json | null };

export type UpdatePolicyRequest_skip_id_ = {
  readonly algorithm?: Algorithm;
  readonly description?: string;
  readonly limit?: number;
  readonly name?: string;
  readonly windowSeconds?: number;
} & { readonly [key: string]: Json | null };

export type UpdatePolicyRequest_skip_value_ = {
  readonly algorithm?: Algorithm;
  readonly description?: string;
  readonly limit?: number;
  readonly name?: string;
  readonly windowSeconds?: number;
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
