import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMyReferralStatsResource } from "./resources/GetMyReferralStatsResource.js";
import { GetReferralCodeResource } from "./resources/GetReferralCodeResource.js";
import { GetReferralCodeStoredResource } from "./resources/GetReferralCodeStoredResource.js";
import { GetReferralResource } from "./resources/GetReferralResource.js";
import { GetRewardResource } from "./resources/GetRewardResource.js";
import { ListMyReferralCodesResource } from "./resources/ListMyReferralCodesResource.js";
import { ListMyReferralsResource } from "./resources/ListMyReferralsResource.js";
import { ListMyRewardsResource } from "./resources/ListMyRewardsResource.js";
import { ListReferralsForCodeResource } from "./resources/ListReferralsForCodeResource.js";
import { ReferralCodeByCodeStringResource } from "./resources/ReferralCodeByCodeStringResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ReferralCode_skip_id_,
  ReferralCodeStored,
  Referral_skip_id_,
  Referral_skip_value_,
  Reward_skip_id_,
  Reward_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetMyReferralStatsParams,
  ListMyReferralCodesParams,
  ListMyReferralsParams,
  ListMyRewardsParams,
  ListReferralsForCodeParams,
  ReferralCode,
  Referral,
  Reward,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly referralCodes: InputDefinition<
    ReferralCode_skip_id_,
    ReferralCodeStored
  >;
  readonly referrals: InputDefinition<Referral_skip_id_, Referral_skip_value_>;
  readonly rewards: InputDefinition<Reward_skip_id_, Reward_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMyReferralStatsResource: ResourceClass<
    GraphCollections,
    GetMyReferralStatsParams
  >;
  readonly getReferralCodeResource: ResourceClass<GraphCollections, Json>;
  readonly getReferralCodeStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getReferralResource: ResourceClass<GraphCollections, Json>;
  readonly getRewardResource: ResourceClass<GraphCollections, Json>;
  readonly listMyReferralCodesResource: ResourceClass<
    GraphCollections,
    ListMyReferralCodesParams
  >;
  readonly listMyReferralsResource: ResourceClass<
    GraphCollections,
    ListMyReferralsParams
  >;
  readonly listMyRewardsResource: ResourceClass<
    GraphCollections,
    ListMyRewardsParams
  >;
  readonly listReferralsForCodeResource: ResourceClass<
    GraphCollections,
    ListReferralsForCodeParams
  >;
  readonly referralCodeByCodeStringResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      referralCodes: new InputDefinition<
        ReferralCode_skip_id_,
        ReferralCodeStored
      >([]),
      referrals: new InputDefinition<Referral_skip_id_, Referral_skip_value_>(
        [],
      ),
      rewards: new InputDefinition<Reward_skip_id_, Reward_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getMyReferralStatsResource: GetMyReferralStatsResource,
      getReferralCodeResource: GetReferralCodeResource,
      getReferralCodeStoredResource: GetReferralCodeStoredResource,
      getReferralResource: GetReferralResource,
      getRewardResource: GetRewardResource,
      listMyReferralCodesResource: ListMyReferralCodesResource,
      listMyReferralsResource: ListMyReferralsResource,
      listMyRewardsResource: ListMyRewardsResource,
      listReferralsForCodeResource: ListReferralsForCodeResource,
      referralCodeByCodeStringResource: ReferralCodeByCodeStringResource,
      getMeResource: getMeResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
