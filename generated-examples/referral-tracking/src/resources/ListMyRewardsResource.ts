import { FilterRewardsByBeneficiaryMapper } from "../mappers/FilterRewardsByBeneficiaryMapper.js";
import type {
  User_skip_id_,
  Reward,
  Reward_skip_id_,
  ListMyRewardsParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyRewardsResourceInputs extends SharedCollections {
  readonly rewardsByBeneficiary: EagerCollection<User_skip_id_, Reward>;
}

export class ListMyRewardsResource implements Resource<ListMyRewardsResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMyRewardsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyRewardsResourceInputs,
    _context: Context,
  ): EagerCollection<Reward_skip_id_, Reward> {
    return inputs.rewardsByBeneficiary.map(
      FilterRewardsByBeneficiaryMapper,
      this.userId,
    );
  }
}
