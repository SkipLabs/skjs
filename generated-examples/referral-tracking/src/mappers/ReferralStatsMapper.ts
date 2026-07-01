import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  ReferralStats,
  Referral,
  RewardAmountMinorUnits,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, when the entry's key does not equal the userId param, emit nothing. Otherwise consult referralsByReferrer for the values indexed by the userId param — each consulted value is one referral row where the caller is the referrer. Count them into totalReferrals; count those whose status field equals the literal 'PENDING' into pendingCount; those equal to 'CONFIRMED' into confirmedCount; those equal to 'REJECTED' into rejectedCount. Consult rewardAmountTotalByUser for the values indexed by the userId param; if the consultation yields no values use zero, otherwise use the first value as totalRewardMinorUnits. Emit one output pair whose key is the literal zero and whose value lists every required field of ReferralStats explicitly: totalReferrals sourced from the count of consulted referrals; pendingCount, confirmedCount, rejectedCount from the per-status counts; totalRewardMinorUnits from the resolved reward sum; currency initialised to the literal 'USD'. When no values are consulted from referralsByReferrer, totalReferrals, pendingCount, confirmedCount, rejectedCount are all zero; when no values are consulted from rewardAmountTotalByUser, totalRewardMinorUnits is zero — the emit still occurs so the api handler always sees a singleton.
export class ReferralStatsMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  0,
  ReferralStats
> {
  constructor(
    private userId: string,
    private referralsByReferrer: EagerCollection<User_skip_id_, Referral>,
    private rewardAmountTotalByUser: EagerCollection<
      User_skip_id_,
      RewardAmountMinorUnits
    >,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[0, ReferralStats]> {
    // > body
    if (key !== this.userId) return [];
    const referrals = this.referralsByReferrer.getArray(this.userId);
    let totalReferrals = 0;
    let pendingCount = 0;
    let confirmedCount = 0;
    let rejectedCount = 0;
    for (const referral of referrals) {
      totalReferrals++;
      if (referral.status === "PENDING") pendingCount++;
      else if (referral.status === "CONFIRMED") confirmedCount++;
      else if (referral.status === "REJECTED") rejectedCount++;
    }
    const rewardValues = this.rewardAmountTotalByUser.getArray(this.userId);
    const first = rewardValues[0];
    const totalRewardMinorUnits = first === undefined ? 0 : first;
    const stats: ReferralStats = {
      totalReferrals,
      pendingCount,
      confirmedCount,
      rejectedCount,
      totalRewardMinorUnits,
      currency: "USD",
    };
    return [[0, stats]];
    // < body
  }
}
