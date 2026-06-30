export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiKey = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly lastUsedAt?: string;
  readonly ownerId: string;
  readonly secretHash: string;
  readonly secretPrefix: string;
};

export type ApiKeyCreated = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly ownerId: string;
  readonly secret: string;
  readonly secretPrefix: string;
};

export type ApiKeyCreated_skip_id_ = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly ownerId: string;
  readonly secret: string;
  readonly secretPrefix: string;
};

export type ApiKeyCreated_skip_value_ = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly ownerId: string;
  readonly secret: string;
  readonly secretPrefix: string;
};

export type ApiKeyList = {
  readonly items: ApiKeyPublic[];
  readonly total: number;
};

export type ApiKeyList_skip_id_ = {
  readonly items: ApiKeyPublic[];
  readonly total: number;
};

export type ApiKeyList_skip_value_ = {
  readonly items: ApiKeyPublic[];
  readonly total: number;
};

export type ApiKeyPublic = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly lastUsedAt?: string;
  readonly ownerId: string;
  readonly secretPrefix: string;
};

export type ApiKeyPublic_skip_id_ = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly lastUsedAt?: string;
  readonly ownerId: string;
  readonly secretPrefix: string;
};

export type ApiKeyPublic_skip_value_ = {
  readonly createdAt: string;
  readonly id: string;
  readonly label: string;
  readonly lastUsedAt?: string;
  readonly ownerId: string;
  readonly secretPrefix: string;
};

export type ApiKeySecret = string;

export type ApiKeySecretHash = string;

export type ApiKey_skip_id_ = string;

export type ApiKey_skip_value_ = {
  readonly createdAt: string;
  readonly label: string;
  readonly lastUsedAt?: string;
  readonly ownerId: string;
  readonly secretHash: string;
  readonly secretPrefix: string;
};

export type Binding = {
  readonly createdAt: string;
  readonly id: string;
  readonly keyId: string;
  readonly ownerId: string;
  readonly policyId: string;
  readonly routePattern?: string;
};

export type BindingList = { readonly items: Binding[] };

export type BindingList_skip_id_ = { readonly items: Binding[] };

export type BindingList_skip_value_ = { readonly items: Binding[] };

export type Binding_skip_id_ = string;

export type Binding_skip_value_ = {
  readonly createdAt: string;
  readonly keyId: string;
  readonly ownerId: string;
  readonly policyId: string;
  readonly routePattern?: string;
};

export type Bucket = {
  readonly count?: number;
  readonly keyId: string;
  readonly kind: PolicyKind;
  readonly lastRefillAt?: string;
  readonly ownerId: string;
  readonly policyId: string;
  readonly tokens?: number;
  readonly windowStartAt?: string;
};

export type BucketKey = { readonly keyId: string; readonly policyId: string };

export type BucketList = { readonly items: BucketState[] };

export type BucketList_skip_id_ = { readonly items: BucketState[] };

export type BucketList_skip_value_ = { readonly items: BucketState[] };

export type BucketState = {
  readonly asOf: string;
  readonly capacity: number;
  readonly keyId: string;
  readonly kind: PolicyKind;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type BucketState_skip_id_ = {
  readonly asOf: string;
  readonly capacity: number;
  readonly keyId: string;
  readonly kind: PolicyKind;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type BucketState_skip_value_ = {
  readonly asOf: string;
  readonly capacity: number;
  readonly keyId: string;
  readonly kind: PolicyKind;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type Bucket_skip_id_ = {
  readonly keyId: string;
  readonly policyId: string;
};

export type Bucket_skip_value_ = {
  readonly count?: number;
  readonly kind: PolicyKind;
  readonly lastRefillAt?: string;
  readonly ownerId: string;
  readonly tokens?: number;
  readonly windowStartAt?: string;
};

export type CheckRateLimitRequest = {
  readonly cost?: number;
  readonly keyId: string;
  readonly route?: string;
  readonly secret: string;
};

export type CheckRateLimitRequest_skip_id_ = {
  readonly cost?: number;
  readonly keyId: string;
  readonly route?: string;
  readonly secret: string;
};

export type CheckRateLimitRequest_skip_value_ = {
  readonly cost?: number;
  readonly keyId: string;
  readonly route?: string;
  readonly secret: string;
};

export type CheckRateLimitResponse = {
  readonly allowed: boolean;
  readonly checkedAt: string;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type CheckRateLimitResponse_skip_id_ = {
  readonly allowed: boolean;
  readonly checkedAt: string;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type CheckRateLimitResponse_skip_value_ = {
  readonly allowed: boolean;
  readonly checkedAt: string;
  readonly policyId: string;
  readonly remaining: number;
  readonly resetAt: string;
};

export type CreateApiKeyRequest = { readonly label: string };

export type CreateApiKeyRequest_skip_id_ = { readonly label: string };

export type CreateApiKeyRequest_skip_value_ = { readonly label: string };

export type CreateBindingRequest = {
  readonly policyId: string;
  readonly routePattern?: string;
};

export type CreateBindingRequest_skip_id_ = {
  readonly policyId: string;
  readonly routePattern?: string;
};

export type CreateBindingRequest_skip_value_ = {
  readonly policyId: string;
  readonly routePattern?: string;
};

export type CreatePolicyRequest = {
  readonly capacity: number;
  readonly kind: PolicyKind;
  readonly name: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type CreatePolicyRequest_skip_id_ = {
  readonly capacity: number;
  readonly kind: PolicyKind;
  readonly name: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type CreatePolicyRequest_skip_value_ = {
  readonly capacity: number;
  readonly kind: PolicyKind;
  readonly name: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type GetApiKeyParams = { readonly keyId: string };

export type GetBindingParams = { readonly bindingId: string };

export type GetPolicyParams = { readonly policyId: string };

export type ListApiKeysParams = { readonly userId: string };

export type ListBindingsByPolicyParams = { readonly policyId: string };

export type ListBindingsForApiKeyParams = { readonly keyId: string };

export type ListBucketsForApiKeyParams = { readonly keyId: string };

export type ListPoliciesParams = { readonly userId: string };

export type ListUsageEventsForApiKeyParams = { readonly keyId: string };

export type Policy = {
  readonly capacity: number;
  readonly createdAt: string;
  readonly id: string;
  readonly kind: PolicyKind;
  readonly name: string;
  readonly ownerId: string;
  readonly refillPerSecond?: number;
  readonly updatedAt?: string;
  readonly windowSeconds?: number;
};

export type PolicyKind = "token_bucket" | "fixed_window";

export type PolicyKind_skip_id_ = "token_bucket" | "fixed_window";

export type PolicyKind_skip_value_ = "token_bucket" | "fixed_window";

export type PolicyList = { readonly items: Policy[]; readonly total: number };

export type PolicyList_skip_id_ = {
  readonly items: Policy[];
  readonly total: number;
};

export type PolicyList_skip_value_ = {
  readonly items: Policy[];
  readonly total: number;
};

export type Policy_skip_id_ = string;

export type Policy_skip_value_ = {
  readonly capacity: number;
  readonly createdAt: string;
  readonly kind: PolicyKind;
  readonly name: string;
  readonly ownerId: string;
  readonly refillPerSecond?: number;
  readonly updatedAt?: string;
  readonly windowSeconds?: number;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdatePolicyRequest = {
  readonly capacity?: number;
  readonly name?: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type UpdatePolicyRequest_skip_id_ = {
  readonly capacity?: number;
  readonly name?: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type UpdatePolicyRequest_skip_value_ = {
  readonly capacity?: number;
  readonly name?: string;
  readonly refillPerSecond?: number;
  readonly windowSeconds?: number;
};

export type UsageEvent = {
  readonly allowed: boolean;
  readonly checkedAt: string;
  readonly cost: number;
  readonly id: string;
  readonly keyId: string;
  readonly ownerId: string;
  readonly policyId: string;
  readonly remainingAfter: number;
  readonly route?: string;
};

export type UsageEventList = {
  readonly items: UsageEvent[];
  readonly total: number;
};

export type UsageEventList_skip_id_ = {
  readonly items: UsageEvent[];
  readonly total: number;
};

export type UsageEventList_skip_value_ = {
  readonly items: UsageEvent[];
  readonly total: number;
};

export type UsageEvent_skip_id_ = string;

export type UsageEvent_skip_value_ = {
  readonly allowed: boolean;
  readonly checkedAt: string;
  readonly cost: number;
  readonly keyId: string;
  readonly ownerId: string;
  readonly policyId: string;
  readonly remainingAfter: number;
  readonly route?: string;
};

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
};
