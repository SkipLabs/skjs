import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { User_skip_id_, Reward, Reward_skip_id_, User } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by beneficiary userId), emit one output pair per value whose key is sourced from the value's id field (the original reward id) and whose value is the value unchanged, when the entry's key equals the userId param. Otherwise emit nothing for that value.
export class FilterRewardsByBeneficiaryMapper implements Mapper<
  User_skip_id_,
  Reward,
  Reward_skip_id_,
  Reward
> {
  constructor(private userId: string) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<Reward>,
    context: Context,
  ): Iterable<[Reward_skip_id_, Reward]> {
    // > body
    const emits: [Reward_skip_id_, Reward][] = [];
    if (key === this.userId) {
      for (const value of values) {
        emits.push([value.id, value]);
      }
    }
    return emits;
    // < body
  }
}
