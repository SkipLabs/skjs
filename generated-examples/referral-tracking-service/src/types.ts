export type PendingCompletedav1jscEnum = "cancelled" | "completed" | "expired" | "pending";

export type Referrer_bonusReferee_bonusEnum = "referrer_bonus" | "referee_bonus";

export type PendingCreditedExpiredEnum = "pending" | "credited" | "expired";

export type UserId = string;

export type UserValue = {
  email: string;
  name: string;
  referralCode: string;
  referredBy: string | null;
  totalReferrals: number;
  totalRewardsEarned: number;
  createdAt: number;
};

export type User = {
  id: UserId;
  email: string;
  name: string;
  referralCode: string;
  referredBy: string | null;
  totalReferrals: number;
  totalRewardsEarned: number;
  createdAt: number;
};

export type ReferralId = string;

export type ReferralValue = {
  referrerId: string;
  refereeId: string;
  referralCode: string;
  status: PendingCompletedav1jscEnum;
  rewardAmount: number;
  createdAt: number;
  completedAt: number | null;
};

export type Referral = {
  id: ReferralId;
  referrerId: string;
  refereeId: string;
  referralCode: string;
  status: PendingCompletedav1jscEnum;
  rewardAmount: number;
  createdAt: number;
  completedAt: number | null;
};

export type RewardId = string;

export type RewardValue = {
  userId: string;
  referralId: string;
  amount: number;
  type: Referrer_bonusReferee_bonusEnum;
  status: PendingCreditedExpiredEnum;
  createdAt: number;
  creditedAt: number | null;
};

export type Reward = {
  id: RewardId;
  userId: string;
  referralId: string;
  amount: number;
  type: Referrer_bonusReferee_bonusEnum;
  status: PendingCreditedExpiredEnum;
  createdAt: number;
  creditedAt: number | null;
};

export type ReferralStatsId = string;

export type ReferralStatsValue = {
  userId: string;
  totalReferrals: number;
  completedReferrals: number;
  pendingReferrals: number;
  totalRewardsEarned: number;
  conversionRate: number;
};

export type ReferralStats = {
  id: ReferralStatsId;
  userId: string;
  totalReferrals: number;
  completedReferrals: number;
  pendingReferrals: number;
  totalRewardsEarned: number;
  conversionRate: number;
};

export type ReferralsByReferrerResourceParams = {
  referrerId: string;
};

export type RewardsByUserResourceParams = {
  userId: string;
};
