import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMySpendingSummaryResource } from "./resources/GetMySpendingSummaryResource.js";
import { GetSubscriptionResource } from "./resources/GetSubscriptionResource.js";
import { GetSubscriptionStoredResource } from "./resources/GetSubscriptionStoredResource.js";
import { ListSubscriptionPaymentsResource } from "./resources/ListSubscriptionPaymentsResource.js";
import { ListSubscriptionsResource } from "./resources/ListSubscriptionsResource.js";
import { PaymentEventsByOwnerResource } from "./resources/PaymentEventsByOwnerResource.js";
import { SubscriptionsByOwnerResource } from "./resources/SubscriptionsByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetSpendingSummaryParams,
  GetSubscriptionParams,
  ListPaymentsByOwnerSubParams,
  ListSubscriptionsParams,
  PaymentEvent,
  Subscription,
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
  readonly paymentEvents: InputDefinition<
    PaymentEvent_skip_id_,
    PaymentEvent_skip_value_
  >;
  readonly subscriptions: InputDefinition<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMySpendingSummaryResource: ResourceClass<
    GraphCollections,
    GetSpendingSummaryParams
  >;
  readonly getSubscriptionResource: ResourceClass<
    GraphCollections,
    GetSubscriptionParams
  >;
  readonly getSubscriptionStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listSubscriptionPaymentsResource: ResourceClass<
    GraphCollections,
    ListPaymentsByOwnerSubParams
  >;
  readonly listSubscriptionsResource: ResourceClass<
    GraphCollections,
    ListSubscriptionsParams
  >;
  readonly paymentEventsByOwnerResource: ResourceClass<GraphCollections, Json>;
  readonly subscriptionsByOwnerResource: ResourceClass<GraphCollections, Json>;
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
      paymentEvents: new InputDefinition<
        PaymentEvent_skip_id_,
        PaymentEvent_skip_value_
      >([]),
      subscriptions: new InputDefinition<
        Subscription_skip_id_,
        Subscription_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getMySpendingSummaryResource: GetMySpendingSummaryResource,
      getSubscriptionResource: GetSubscriptionResource,
      getSubscriptionStoredResource: GetSubscriptionStoredResource,
      listSubscriptionPaymentsResource: ListSubscriptionPaymentsResource,
      listSubscriptionsResource: ListSubscriptionsResource,
      paymentEventsByOwnerResource: PaymentEventsByOwnerResource,
      subscriptionsByOwnerResource: SubscriptionsByOwnerResource,
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
