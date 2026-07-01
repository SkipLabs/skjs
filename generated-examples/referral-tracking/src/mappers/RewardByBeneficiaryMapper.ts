import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Reward_skip_id_,
  Reward_skip_value_,
  User_skip_id_,
  Reward,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each reward entry, emit one output pair whose key is sourced from the entry's value's beneficiaryUserId field, and whose value lists every required field of Reward explicitly: id sourced from the entry's key (the original Reward.id); referralId sourced from the entry's value's referralId field; beneficiaryUserId sourced from the entry's value's beneficiaryUserId field; amount sourced from the entry's value's amount field; currency sourced from the entry's value's currency field; createdAt sourced from the entry's value's createdAt field. The original Reward.id from the entry's key is preserved inside the value's id field so downstream consumers reading value.id have access to it.
export class RewardByBeneficiaryMapper implements Mapper<
  Reward_skip_id_,
  Reward_skip_value_,
  User_skip_id_,
  Reward
> {
  mapEntry(
    key: Reward_skip_id_,
    values: Values<Reward_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Reward]> {
    // > body
    const emits: [User_skip_id_, Reward][] = [];
    for (const value of values.toArray()) {
      const reward: Reward = {
        id: key,
        referralId: value.referralId,
        beneficiaryUserId: value.beneficiaryUserId,
        amount: value.amount,
        currency: value.currency,
        createdAt: value.createdAt,
      };
      emits.push([value.beneficiaryUserId, reward]);
    }
    return emits;
    // < body
  }
}
