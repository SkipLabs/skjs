import { BindingByKeyIdMapper } from "./mappers/BindingByKeyIdMapper.js";
import { BindingByPolicyIdMapper } from "./mappers/BindingByPolicyIdMapper.js";
import { BucketByKeyIdMapper } from "./mappers/BucketByKeyIdMapper.js";
import { UsageEventByKeyIdMapper } from "./mappers/UsageEventByKeyIdMapper.js";
import type {
  ApiKey_skip_id_,
  ApiKey,
  ApiKey_skip_value_,
  Binding_skip_id_,
  Binding,
  Binding_skip_value_,
  BucketKey,
  Bucket_skip_value_,
  Bucket,
  Policy_skip_id_,
  Policy,
  Policy_skip_value_,
  UsageEvent_skip_id_,
  UsageEvent,
  UsageEvent_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly apiKeys: EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_>;
  readonly bindings: EagerCollection<Binding_skip_id_, Binding_skip_value_>;
  readonly buckets: EagerCollection<BucketKey, Bucket_skip_value_>;
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
  readonly usageEvents: EagerCollection<
    UsageEvent_skip_id_,
    UsageEvent_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly apiKeys: EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_>;
  readonly bindings: EagerCollection<Binding_skip_id_, Binding_skip_value_>;
  readonly bindingsByKey: EagerCollection<ApiKey_skip_id_, Binding>;
  readonly bindingsByPolicy: EagerCollection<Policy_skip_id_, Binding>;
  readonly buckets: EagerCollection<BucketKey, Bucket_skip_value_>;
  readonly bucketsByKey: EagerCollection<ApiKey_skip_id_, Bucket>;
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
  readonly usageByKey: EagerCollection<ApiKey_skip_id_, UsageEvent>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_apiKeys = inputs.apiKeys;
  const output_bindings = inputs.bindings;
  const output_bindingsByKey = inputs.bindings.map(BindingByKeyIdMapper);
  const output_bindingsByPolicy = inputs.bindings.map(BindingByPolicyIdMapper);
  const output_buckets = inputs.buckets;
  const output_bucketsByKey = inputs.buckets.map(BucketByKeyIdMapper);
  const output_policies = inputs.policies;
  const output_usageByKey = inputs.usageEvents.map(UsageEventByKeyIdMapper);
  const output_users = inputs.users;
  return {
    apiKeys: output_apiKeys,
    bindings: output_bindings,
    bindingsByKey: output_bindingsByKey,
    bindingsByPolicy: output_bindingsByPolicy,
    buckets: output_buckets,
    bucketsByKey: output_bucketsByKey,
    policies: output_policies,
    usageByKey: output_usageByKey,
    users: output_users,
  };
}
