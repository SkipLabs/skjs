import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetReferralCodeByIdResource } from "./resources/GetReferralCodeByIdResource.js";
import { GetReferralEventByIdResource } from "./resources/GetReferralEventByIdResource.js";
import { GetUserByIdResource } from "./resources/GetUserByIdResource.js";
import { ListReferralCodesResource } from "./resources/ListReferralCodesResource.js";
import { ListReferralEventsResource } from "./resources/ListReferralEventsResource.js";
import { ReferralCodeByCodeValueResource } from "./resources/ReferralCodeByCodeValueResource.js";
import { ReferralCodeStatsResource } from "./resources/ReferralCodeStatsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetReferralCodeByIdParams,
  GetReferralEventByIdParams,
  GetUserByIdParams,
  ListReferralCodesParams,
  ListReferralEventsParams,
  ReferralCode,
  ReferralEvent,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly referralCodes: InputDefinition<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
  readonly referralEvents: InputDefinition<
    ReferralEvent_skip_id_,
    ReferralEvent_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getReferralCodeByIdResource: ResourceClass<
    GraphCollections,
    GetReferralCodeByIdParams
  >;
  readonly getReferralEventByIdResource: ResourceClass<
    GraphCollections,
    GetReferralEventByIdParams
  >;
  readonly getUserByIdResource: ResourceClass<
    GraphCollections,
    GetUserByIdParams
  >;
  readonly listReferralCodesResource: ResourceClass<
    GraphCollections,
    ListReferralCodesParams
  >;
  readonly listReferralEventsResource: ResourceClass<
    GraphCollections,
    ListReferralEventsParams
  >;
  readonly referralCodeByCodeValueResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly referralCodeStatsResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      referralCodes: new InputDefinition<
        ReferralCode_skip_id_,
        ReferralCode_skip_value_
      >([]),
      referralEvents: new InputDefinition<
        ReferralEvent_skip_id_,
        ReferralEvent_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getReferralCodeByIdResource: GetReferralCodeByIdResource,
      getReferralEventByIdResource: GetReferralEventByIdResource,
      getUserByIdResource: GetUserByIdResource,
      listReferralCodesResource: ListReferralCodesResource,
      listReferralEventsResource: ListReferralEventsResource,
      referralCodeByCodeValueResource: ReferralCodeByCodeValueResource,
      referralCodeStatsResource: ReferralCodeStatsResource,
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
