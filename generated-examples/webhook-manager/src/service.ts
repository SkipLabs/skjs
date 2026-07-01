import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetDeliveryResource } from "./resources/GetDeliveryResource.js";
import { GetSubscriptionResource } from "./resources/GetSubscriptionResource.js";
import { GetWebhookResource } from "./resources/GetWebhookResource.js";
import { ListDeliveriesByWebhookResource } from "./resources/ListDeliveriesByWebhookResource.js";
import { ListDeliveriesForWebhookResource } from "./resources/ListDeliveriesForWebhookResource.js";
import { ListSubscriptionsForWebhookResource } from "./resources/ListSubscriptionsForWebhookResource.js";
import { ListWebhooksResource } from "./resources/ListWebhooksResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Delivery_skip_id_,
  Delivery_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Webhook_skip_id_,
  WebhookStored,
  ListDeliveriesForWebhookParams,
  ListWebhooksParams,
  Delivery,
  Subscription,
  User,
  Webhook,
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
  readonly deliveries: InputDefinition<Delivery_skip_id_, Delivery_skip_value_>;
  readonly subscriptions: InputDefinition<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly webhooks: InputDefinition<Webhook_skip_id_, WebhookStored>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getDeliveryResource: ResourceClass<GraphCollections, Json>;
  readonly getSubscriptionResource: ResourceClass<GraphCollections, Json>;
  readonly getWebhookResource: ResourceClass<GraphCollections, Json>;
  readonly listDeliveriesByWebhookResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listDeliveriesForWebhookResource: ResourceClass<
    GraphCollections,
    ListDeliveriesForWebhookParams
  >;
  readonly listSubscriptionsForWebhookResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listWebhooksResource: ResourceClass<
    GraphCollections,
    ListWebhooksParams
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
      deliveries: new InputDefinition<Delivery_skip_id_, Delivery_skip_value_>(
        [],
      ),
      subscriptions: new InputDefinition<
        Subscription_skip_id_,
        Subscription_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      webhooks: new InputDefinition<Webhook_skip_id_, WebhookStored>([]),
    };
    this.resources = {
      getDeliveryResource: GetDeliveryResource,
      getSubscriptionResource: GetSubscriptionResource,
      getWebhookResource: GetWebhookResource,
      listDeliveriesByWebhookResource: ListDeliveriesByWebhookResource,
      listDeliveriesForWebhookResource: ListDeliveriesForWebhookResource,
      listSubscriptionsForWebhookResource: ListSubscriptionsForWebhookResource,
      listWebhooksResource: ListWebhooksResource,
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
