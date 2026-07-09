import { ConsumptionEventByPolicyMapper } from "./mappers/ConsumptionEventByPolicyMapper.js";
import type {
  ConsumptionEvent_skip_id_,
  ConsumptionEvent,
  ConsumptionEvent_skip_value_,
  Policy_skip_id_,
  Policy,
  Policy_skip_value_,
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
  readonly consumptionEvents: EagerCollection<
    ConsumptionEvent_skip_id_,
    ConsumptionEvent_skip_value_
  >;
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly consumptionEvents: EagerCollection<
    ConsumptionEvent_skip_id_,
    ConsumptionEvent_skip_value_
  >;
  readonly eventsByPolicy: EagerCollection<Policy_skip_id_, ConsumptionEvent>;
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const eventsByPolicy = inputs.consumptionEvents.map(
    ConsumptionEventByPolicyMapper,
  );
  const output_consumptionEvents = inputs.consumptionEvents;
  const output_eventsByPolicy = eventsByPolicy;
  const output_policies = inputs.policies;
  const output_users = inputs.users;
  return {
    consumptionEvents: output_consumptionEvents,
    eventsByPolicy: output_eventsByPolicy,
    policies: output_policies,
    users: output_users,
  };
}
