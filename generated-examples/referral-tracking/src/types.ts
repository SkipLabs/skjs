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

export type CreateReferralCodeRequest = {
  readonly code?: string;
  readonly note?: string;
} & { readonly [key: string]: Json | null };

export type CreateReferralCodeRequest_skip_id_ = {
  readonly code?: string;
  readonly note?: string;
} & { readonly [key: string]: Json | null };

export type CreateReferralCodeRequest_skip_value_ = {
  readonly code?: string;
  readonly note?: string;
} & { readonly [key: string]: Json | null };

export type CreateReferralRequest = { readonly code: string } & {
  readonly [key: string]: Json | null;
};

export type CreateReferralRequest_skip_id_ = { readonly code: string } & {
  readonly [key: string]: Json | null;
};

export type CreateReferralRequest_skip_value_ = { readonly code: string } & {
  readonly [key: string]: Json | null;
};

export type GetMyReferralStatsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListMyReferralCodesParams = {
  readonly status?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListMyReferralsParams = {
  readonly role?: string;
  readonly status?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListMyRewardsParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListReferralsForCodeParams = {
  readonly referralCodeId: string;
  readonly since?: string;
  readonly status?: string;
  readonly until?: string;
} & { readonly [key: string]: Json | null };

export type RedemptionCount = number;

export type Referral = {
  readonly confirmedAt?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly referralCodeId: string;
  readonly referredUserId: string;
  readonly referrerUserId: string;
  readonly rejectedAt?: string;
  readonly rejectionReason?: string;
  readonly status: ReferralStatus;
} & { readonly [key: string]: Json | null };

export type ReferralCode = {
  readonly code: string;
  readonly createdAt: string;
  readonly id: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly redemptionCount: number;
  readonly status: ReferralCodeStatus;
} & { readonly [key: string]: Json | null };

export type ReferralCodeList = {
  readonly items: ReferralCode[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralCodeList_skip_id_ = {
  readonly items: ReferralCode[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralCodeList_skip_value_ = {
  readonly items: ReferralCode[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralCodeStatus = "ACTIVE" | "DISABLED";

export type ReferralCodeStatus_skip_id_ = "ACTIVE" | "DISABLED";

export type ReferralCodeStatus_skip_value_ = "ACTIVE" | "DISABLED";

export type ReferralCodeStored = {
  readonly code: string;
  readonly createdAt: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly status: "ACTIVE" | "DISABLED";
} & { readonly [key: string]: Json | null };

export type ReferralCodeStoredWithId = {
  readonly code: string;
  readonly createdAt: string;
  readonly id: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly status: "ACTIVE" | "DISABLED";
} & { readonly [key: string]: Json | null };

export type ReferralCodeString = string;

export type ReferralCode_skip_id_ = string;

export type ReferralCode_skip_value_ = {
  readonly code: string;
  readonly createdAt: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly redemptionCount: number;
  readonly status: ReferralCodeStatus;
} & { readonly [key: string]: Json | null };

export type ReferralList = {
  readonly items: Referral[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralList_skip_id_ = {
  readonly items: Referral[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralList_skip_value_ = {
  readonly items: Referral[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type ReferralStats = {
  readonly confirmedCount: number;
  readonly currency: string;
  readonly pendingCount: number;
  readonly rejectedCount: number;
  readonly totalReferrals: number;
  readonly totalRewardMinorUnits: number;
} & { readonly [key: string]: Json | null };

export type ReferralStatsAccum = {
  readonly confirmedCount: number;
  readonly pendingCount: number;
  readonly rejectedCount: number;
  readonly totalReferrals: number;
} & { readonly [key: string]: Json | null };

export type ReferralStats_skip_id_ = {
  readonly confirmedCount: number;
  readonly currency: string;
  readonly pendingCount: number;
  readonly rejectedCount: number;
  readonly totalReferrals: number;
  readonly totalRewardMinorUnits: number;
} & { readonly [key: string]: Json | null };

export type ReferralStats_skip_value_ = {
  readonly confirmedCount: number;
  readonly currency: string;
  readonly pendingCount: number;
  readonly rejectedCount: number;
  readonly totalReferrals: number;
  readonly totalRewardMinorUnits: number;
} & { readonly [key: string]: Json | null };

export type ReferralStatus = "PENDING" | "CONFIRMED" | "REJECTED";

export type ReferralStatus_skip_id_ = "PENDING" | "CONFIRMED" | "REJECTED";

export type ReferralStatus_skip_value_ = "PENDING" | "CONFIRMED" | "REJECTED";

export type Referral_skip_id_ = string;

export type Referral_skip_value_ = {
  readonly confirmedAt?: string;
  readonly createdAt: string;
  readonly referralCodeId: string;
  readonly referredUserId: string;
  readonly referrerUserId: string;
  readonly rejectedAt?: string;
  readonly rejectionReason?: string;
  readonly status: ReferralStatus;
} & { readonly [key: string]: Json | null };

export type RejectReferralRequest = { readonly rejectionReason?: string } & {
  readonly [key: string]: Json | null;
};

export type RejectReferralRequest_skip_id_ = {
  readonly rejectionReason?: string;
} & { readonly [key: string]: Json | null };

export type RejectReferralRequest_skip_value_ = {
  readonly rejectionReason?: string;
} & { readonly [key: string]: Json | null };

export type Reward = {
  readonly amount: number;
  readonly beneficiaryUserId: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly id: string;
  readonly referralId: string;
} & { readonly [key: string]: Json | null };

export type RewardAmountMinorUnits = number;

export type RewardList = {
  readonly items: Reward[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type RewardList_skip_id_ = {
  readonly items: Reward[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type RewardList_skip_value_ = {
  readonly items: Reward[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Reward_skip_id_ = string;

export type Reward_skip_value_ = {
  readonly amount: number;
  readonly beneficiaryUserId: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly referralId: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateReferralCodeRequest = {
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
} & { readonly [key: string]: Json | null };

export type UpdateReferralCodeRequest_skip_id_ = {
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
} & { readonly [key: string]: Json | null };

export type UpdateReferralCodeRequest_skip_value_ = {
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
