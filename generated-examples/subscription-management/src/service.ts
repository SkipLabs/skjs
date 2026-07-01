import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPaymentResource } from "./resources/GetPaymentResource.js";
import { GetSubscriptionResource } from "./resources/GetSubscriptionResource.js";
import { ListSubscriptionsResource } from "./resources/ListSubscriptionsResource.js";
import { PaymentsBySubscriptionResource } from "./resources/PaymentsBySubscriptionResource.js";
import { SubscriptionsByOwnerResource } from "./resources/SubscriptionsByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Payment_skip_id_,
  Payment_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListSubscriptionsParams,
  Payment,
  Subscription,
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
  readonly payments: InputDefinition<Payment_skip_id_, Payment_skip_value_>;
  readonly subscriptions: InputDefinition<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPaymentResource: ResourceClass<GraphCollections, Json>;
  readonly getSubscriptionResource: ResourceClass<GraphCollections, Json>;
  readonly listSubscriptionsResource: ResourceClass<
    GraphCollections,
    ListSubscriptionsParams
  >;
  readonly paymentsBySubscriptionResource: ResourceClass<
    GraphCollections,
    Json
  >;
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
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      payments: new InputDefinition<Payment_skip_id_, Payment_skip_value_>([]),
      subscriptions: new InputDefinition<
        Subscription_skip_id_,
        Subscription_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getPaymentResource: GetPaymentResource,
      getSubscriptionResource: GetSubscriptionResource,
      listSubscriptionsResource: ListSubscriptionsResource,
      paymentsBySubscriptionResource: PaymentsBySubscriptionResource,
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
