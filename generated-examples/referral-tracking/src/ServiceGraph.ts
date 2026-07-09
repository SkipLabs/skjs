import { GetReferralCodeAssembleMapper } from "./mappers/GetReferralCodeAssembleMapper.js";
import { ReferralByCodeIdMapper } from "./mappers/ReferralByCodeIdMapper.js";
import { ReferralByReferrerMapper } from "./mappers/ReferralByReferrerMapper.js";
import { ReferralCodeByCodeStringMapper } from "./mappers/ReferralCodeByCodeStringMapper.js";
import { ReferralCodeByOwnerMapper } from "./mappers/ReferralCodeByOwnerMapper.js";
import { ReferralCountByCodeMapper } from "./mappers/ReferralCountByCodeMapper.js";
import { RewardAmountByBeneficiaryMapper } from "./mappers/RewardAmountByBeneficiaryMapper.js";
import { RewardByBeneficiaryMapper } from "./mappers/RewardByBeneficiaryMapper.js";
import { SumNumberReducer } from "./reducers/SumNumberReducer.js";
import { SumRewardAmountReducer } from "./reducers/SumRewardAmountReducer.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode,
  ReferralCodeStored,
  Referral_skip_id_,
  Referral,
  Referral_skip_value_,
  Reward_skip_id_,
  Reward,
  Reward_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ReferralCode_skip_value_,
  ReferralCodeString,
  ReferralCodeStoredWithId,
  RewardAmountMinorUnits,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCodeStored
  >;
  readonly referrals: EagerCollection<Referral_skip_id_, Referral_skip_value_>;
  readonly rewards: EagerCollection<Reward_skip_id_, Reward_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCodeStored
  >;
  readonly referralCodesAssembled: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
  readonly referralCodesByCodeString: EagerCollection<
    ReferralCodeString,
    ReferralCodeStoredWithId
  >;
  readonly referralCodesByOwner: EagerCollection<User_skip_id_, ReferralCode>;
  readonly referrals: EagerCollection<Referral_skip_id_, Referral_skip_value_>;
  readonly referralsByCodeId: EagerCollection<ReferralCode_skip_id_, Referral>;
  readonly referralsByReferrer: EagerCollection<User_skip_id_, Referral>;
  readonly rewardAmountTotalByUser: EagerCollection<
    User_skip_id_,
    RewardAmountMinorUnits
  >;
  readonly rewards: EagerCollection<Reward_skip_id_, Reward_skip_value_>;
  readonly rewardsByBeneficiary: EagerCollection<User_skip_id_, Reward>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_referralCodes = inputs.referralCodes;
  const referralCountByCodeRaw = inputs.referrals.map(
    ReferralCountByCodeMapper,
  );
  const redemptionCountByCode = referralCountByCodeRaw.reduce(SumNumberReducer);
  const referralCodesAssembled = inputs.referralCodes.map(
    GetReferralCodeAssembleMapper,
    redemptionCountByCode,
  );
  const output_referralCodesAssembled = referralCodesAssembled;
  const referralCodesByCodeString = inputs.referralCodes.map(
    ReferralCodeByCodeStringMapper,
  );
  const output_referralCodesByCodeString = referralCodesByCodeString;
  const referralCodesByOwner = inputs.referralCodes.map(
    ReferralCodeByOwnerMapper,
    redemptionCountByCode,
  );
  const output_referralCodesByOwner = referralCodesByOwner;
  const output_referrals = inputs.referrals;
  const referralsByCodeId = inputs.referrals.map(ReferralByCodeIdMapper);
  const output_referralsByCodeId = referralsByCodeId;
  const referralsByReferrer = inputs.referrals.map(ReferralByReferrerMapper);
  const output_referralsByReferrer = referralsByReferrer;
  const rewardAmountByBeneficiaryRaw = inputs.rewards.map(
    RewardAmountByBeneficiaryMapper,
  );
  const rewardAmountTotalByUser = rewardAmountByBeneficiaryRaw.reduce(
    SumRewardAmountReducer,
  );
  const output_rewardAmountTotalByUser = rewardAmountTotalByUser;
  const output_rewards = inputs.rewards;
  const rewardsByBeneficiary = inputs.rewards.map(RewardByBeneficiaryMapper);
  const output_rewardsByBeneficiary = rewardsByBeneficiary;
  const output_users = inputs.users;
  return {
    referralCodes: output_referralCodes,
    referralCodesAssembled: output_referralCodesAssembled,
    referralCodesByCodeString: output_referralCodesByCodeString,
    referralCodesByOwner: output_referralCodesByOwner,
    referrals: output_referrals,
    referralsByCodeId: output_referralsByCodeId,
    referralsByReferrer: output_referralsByReferrer,
    rewardAmountTotalByUser: output_rewardAmountTotalByUser,
    rewards: output_rewards,
    rewardsByBeneficiary: output_rewardsByBeneficiary,
    users: output_users,
  };
}
