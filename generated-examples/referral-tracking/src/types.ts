export type ACTIVEINACTIVE = "ACTIVE" | "INACTIVE";

export type ACTIVEINACTIVE_skip_id_ = "ACTIVE" | "INACTIVE";

export type ACTIVEINACTIVE_skip_value_ = "ACTIVE" | "INACTIVE";

export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateReferralCodeRequest = {
  readonly code?: string;
  readonly expiresAt?: string;
  readonly note?: string;
};

export type CreateReferralCodeRequest_skip_id_ = {
  readonly code?: string;
  readonly expiresAt?: string;
  readonly note?: string;
};

export type CreateReferralCodeRequest_skip_value_ = {
  readonly code?: string;
  readonly expiresAt?: string;
  readonly note?: string;
};

export type CreateReferralEventRequest = {
  readonly code: string;
  readonly kind: ReferralEventKind;
  readonly metadata?: string;
};

export type CreateReferralEventRequest_skip_id_ = {
  readonly code: string;
  readonly kind: ReferralEventKind;
  readonly metadata?: string;
};

export type CreateReferralEventRequest_skip_value_ = {
  readonly code: string;
  readonly kind: ReferralEventKind;
  readonly metadata?: string;
};

export type GetMeParams = { readonly userId: string };

export type GetReferralCodeByIdParams = { readonly referralCodeId: string };

export type GetReferralEventByIdParams = { readonly referralEventId: string };

export type GetUserByIdParams = { readonly userId: string };

export type ListReferralCodesParams = {
  readonly code?: string;
  readonly ownerId?: string;
  readonly status?: string;
};

export type ListReferralEventsParams = {
  readonly kind?: string;
  readonly referralCodeId?: string;
  readonly referredUserId?: string;
  readonly referrerUserId?: string;
};

export type ReferralCode = {
  readonly code: string;
  readonly createdAt: string;
  readonly expiresAt?: string;
  readonly id: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly status: ACTIVEINACTIVE;
};

export type ReferralCodeList = {
  readonly items: ReferralCode[];
  readonly total: number;
};

export type ReferralCodeList_skip_id_ = {
  readonly items: ReferralCode[];
  readonly total: number;
};

export type ReferralCodeList_skip_value_ = {
  readonly items: ReferralCode[];
  readonly total: number;
};

export type ReferralCodeStats = {
  readonly activationCount: number;
  readonly clickCount: number;
  readonly referralCodeId: string;
  readonly rewardGrantedCount: number;
  readonly signupCount: number;
  readonly uniqueReferredUserCount: number;
};

export type ReferralCodeStatsAccum = {
  readonly activationCount: number;
  readonly clickCount: number;
  readonly referredUserCounts: Record<string, number>;
  readonly rewardGrantedCount: number;
  readonly signupCount: number;
};

export type ReferralCodeStatsParams = { readonly referralCodeId: string };

export type ReferralCodeStats_skip_id_ = {
  readonly activationCount: number;
  readonly clickCount: number;
  readonly referralCodeId: string;
  readonly rewardGrantedCount: number;
  readonly signupCount: number;
  readonly uniqueReferredUserCount: number;
};

export type ReferralCodeStats_skip_value_ = {
  readonly activationCount: number;
  readonly clickCount: number;
  readonly referralCodeId: string;
  readonly rewardGrantedCount: number;
  readonly signupCount: number;
  readonly uniqueReferredUserCount: number;
};

export type ReferralCodeStatus = "ACTIVE" | "INACTIVE";

export type ReferralCodeStatus_skip_id_ = "ACTIVE" | "INACTIVE";

export type ReferralCodeStatus_skip_value_ = "ACTIVE" | "INACTIVE";

export type ReferralCodeValueKey = string;

export type ReferralCode_skip_id_ = string;

export type ReferralCode_skip_value_ = {
  readonly code: string;
  readonly createdAt: string;
  readonly expiresAt?: string;
  readonly note?: string;
  readonly ownerId: string;
  readonly status: ACTIVEINACTIVE;
};

export type ReferralEvent = {
  readonly id: string;
  readonly kind: ReferralEventKind;
  readonly metadata?: string;
  readonly occurredAt: string;
  readonly referralCodeId: string;
  readonly referredUserId: string;
  readonly referrerUserId: string;
};

export type ReferralEventKind =
  | "CLICK"
  | "SIGNUP"
  | "ACTIVATION"
  | "REWARD_GRANTED";

export type ReferralEventKind_skip_id_ =
  | "CLICK"
  | "SIGNUP"
  | "ACTIVATION"
  | "REWARD_GRANTED";

export type ReferralEventKind_skip_value_ =
  | "CLICK"
  | "SIGNUP"
  | "ACTIVATION"
  | "REWARD_GRANTED";

export type ReferralEventList = {
  readonly items: ReferralEvent[];
  readonly total: number;
};

export type ReferralEventList_skip_id_ = {
  readonly items: ReferralEvent[];
  readonly total: number;
};

export type ReferralEventList_skip_value_ = {
  readonly items: ReferralEvent[];
  readonly total: number;
};

export type ReferralEvent_skip_id_ = string;

export type ReferralEvent_skip_value_ = {
  readonly kind: ReferralEventKind;
  readonly metadata?: string;
  readonly occurredAt: string;
  readonly referralCodeId: string;
  readonly referredUserId: string;
  readonly referrerUserId: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateReferralCodeRequest = {
  readonly expiresAt?: string;
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
};

export type UpdateReferralCodeRequest_skip_id_ = {
  readonly expiresAt?: string;
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
};

export type UpdateReferralCodeRequest_skip_value_ = {
  readonly expiresAt?: string;
  readonly note?: string;
  readonly status?: ReferralCodeStatus;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};
