import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Reward_skip_id_,
  Reward_skip_value_,
  User_skip_id_,
  RewardAmountMinorUnits,
  Reward,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each reward entry, emit one output pair whose key is sourced from the entry's value's beneficiaryUserId field and whose value is sourced from the entry's value's amount field. The original Reward.id (from the entry's key) is dropped: this collection is a per-user aggregation feed for SumRewardAmountReducer which sums amounts into rewardAmountTotalByUser, and individual reward row identities are not needed downstream (rewardsByBeneficiary is the sibling collection for enumerating rows).
export class RewardAmountByBeneficiaryMapper implements Mapper<
  Reward_skip_id_,
  Reward_skip_value_,
  User_skip_id_,
  RewardAmountMinorUnits
> {
  mapEntry(
    key: Reward_skip_id_,
    values: Values<Reward_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, RewardAmountMinorUnits]> {
    // > body
    const emits: [User_skip_id_, RewardAmountMinorUnits][] = [];
    for (const value of values.toArray()) {
      emits.push([value.beneficiaryUserId, value.amount]);
    }
    return emits;
    // < body
  }
}
