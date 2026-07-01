import { ReferralStatsMapper } from "../mappers/ReferralStatsMapper.js";
import type {
  User_skip_id_,
  Referral,
  RewardAmountMinorUnits,
  User_skip_value_,
  ReferralStats,
  GetMyReferralStatsParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMyReferralStatsResourceInputs extends SharedCollections {
  readonly referralsByReferrer: EagerCollection<User_skip_id_, Referral>;
  readonly rewardAmountTotalByUser: EagerCollection<
    User_skip_id_,
    RewardAmountMinorUnits
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetMyReferralStatsResource implements Resource<GetMyReferralStatsResourceInputs> {
  private readonly userId: string;

  constructor(params: GetMyReferralStatsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMyReferralStatsResourceInputs,
    _context: Context,
  ): EagerCollection<0, ReferralStats> {
    return inputs.users.map(
      ReferralStatsMapper,
      this.userId,
      inputs.referralsByReferrer,
      inputs.rewardAmountTotalByUser,
    );
  }
}
