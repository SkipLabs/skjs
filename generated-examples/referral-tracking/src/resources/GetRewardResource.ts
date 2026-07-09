import type { Reward_skip_id_, Reward_skip_value_, Reward } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetRewardResourceInputs extends SharedCollections {
  readonly rewards: EagerCollection<Reward_skip_id_, Reward_skip_value_>;
}

export class GetRewardResource implements Resource<GetRewardResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetRewardResourceInputs,
    _context: Context,
  ): EagerCollection<Reward_skip_id_, Reward_skip_value_> {
    return inputs.rewards;
  }
}
