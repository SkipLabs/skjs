import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { BindingsByKeyResource } from "./resources/BindingsByKeyResource.js";
import { GetApiKeyResource } from "./resources/GetApiKeyResource.js";
import { GetBindingResource } from "./resources/GetBindingResource.js";
import { GetBucketResource } from "./resources/GetBucketResource.js";
import { GetPolicyResource } from "./resources/GetPolicyResource.js";
import { ListApiKeysResource } from "./resources/ListApiKeysResource.js";
import { ListBindingsByPolicyResource } from "./resources/ListBindingsByPolicyResource.js";
import { ListBindingsForApiKeyResource } from "./resources/ListBindingsForApiKeyResource.js";
import { ListBucketsForApiKeyResource } from "./resources/ListBucketsForApiKeyResource.js";
import { ListPoliciesResource } from "./resources/ListPoliciesResource.js";
import { ListUsageEventsForApiKeyResource } from "./resources/ListUsageEventsForApiKeyResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ApiKey_skip_id_,
  ApiKey_skip_value_,
  Binding_skip_id_,
  Binding_skip_value_,
  BucketKey,
  Bucket_skip_value_,
  Policy_skip_id_,
  Policy_skip_value_,
  UsageEvent_skip_id_,
  UsageEvent_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListApiKeysParams,
  ListBindingsByPolicyParams,
  ListBindingsForApiKeyParams,
  ListBucketsForApiKeyParams,
  ListPoliciesParams,
  ListUsageEventsForApiKeyParams,
  ApiKey,
  Binding,
  Bucket,
  Policy,
  UsageEvent,
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
  readonly apiKeys: InputDefinition<ApiKey_skip_id_, ApiKey_skip_value_>;
  readonly bindings: InputDefinition<Binding_skip_id_, Binding_skip_value_>;
  readonly buckets: InputDefinition<BucketKey, Bucket_skip_value_>;
  readonly policies: InputDefinition<Policy_skip_id_, Policy_skip_value_>;
  readonly usageEvents: InputDefinition<
    UsageEvent_skip_id_,
    UsageEvent_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly bindingsByKeyResource: ResourceClass<GraphCollections, Json>;
  readonly getApiKeyResource: ResourceClass<GraphCollections, Json>;
  readonly getBindingResource: ResourceClass<GraphCollections, Json>;
  readonly getBucketResource: ResourceClass<GraphCollections, Json>;
  readonly getPolicyResource: ResourceClass<GraphCollections, Json>;
  readonly listApiKeysResource: ResourceClass<
    GraphCollections,
    ListApiKeysParams
  >;
  readonly listBindingsByPolicyResource: ResourceClass<
    GraphCollections,
    ListBindingsByPolicyParams
  >;
  readonly listBindingsForApiKeyResource: ResourceClass<
    GraphCollections,
    ListBindingsForApiKeyParams
  >;
  readonly listBucketsForApiKeyResource: ResourceClass<
    GraphCollections,
    ListBucketsForApiKeyParams
  >;
  readonly listPoliciesResource: ResourceClass<
    GraphCollections,
    ListPoliciesParams
  >;
  readonly listUsageEventsForApiKeyResource: ResourceClass<
    GraphCollections,
    ListUsageEventsForApiKeyParams
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

  constructor() {
    this.inputs = {
      apiKeys: new InputDefinition<ApiKey_skip_id_, ApiKey_skip_value_>([]),
      bindings: new InputDefinition<Binding_skip_id_, Binding_skip_value_>([]),
      buckets: new InputDefinition<BucketKey, Bucket_skip_value_>([]),
      policies: new InputDefinition<Policy_skip_id_, Policy_skip_value_>([]),
      usageEvents: new InputDefinition<
        UsageEvent_skip_id_,
        UsageEvent_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      bindingsByKeyResource: BindingsByKeyResource,
      getApiKeyResource: GetApiKeyResource,
      getBindingResource: GetBindingResource,
      getBucketResource: GetBucketResource,
      getPolicyResource: GetPolicyResource,
      listApiKeysResource: ListApiKeysResource,
      listBindingsByPolicyResource: ListBindingsByPolicyResource,
      listBindingsForApiKeyResource: ListBindingsForApiKeyResource,
      listBucketsForApiKeyResource: ListBucketsForApiKeyResource,
      listPoliciesResource: ListPoliciesResource,
      listUsageEventsForApiKeyResource: ListUsageEventsForApiKeyResource,
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
