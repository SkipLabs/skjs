import { HeartbeatByComponentMapper } from "./mappers/HeartbeatByComponentMapper.js";
import { SystemHealthAggregateMapper } from "./mappers/SystemHealthAggregateMapper.js";
import { SystemHealthShuffleMapper } from "./mappers/SystemHealthShuffleMapper.js";
import type {
  Component_skip_id_,
  Component,
  ComponentStored,
  Heartbeat_skip_id_,
  Heartbeat,
  Heartbeat_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ComponentIdKey,
  SystemHealthAggregate,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly components: EagerCollection<Component_skip_id_, ComponentStored>;
  readonly heartbeats: EagerCollection<
    Heartbeat_skip_id_,
    Heartbeat_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly components: EagerCollection<Component_skip_id_, ComponentStored>;
  readonly heartbeatsByComponent: EagerCollection<ComponentIdKey, Heartbeat>;
  readonly systemHealthAggregate: EagerCollection<0, SystemHealthAggregate>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const componentsShuffled = inputs.components.map(SystemHealthShuffleMapper);
  const heartbeatsByComponent = inputs.heartbeats.map(
    HeartbeatByComponentMapper,
  );
  const output_components = inputs.components;
  const output_heartbeatsByComponent = heartbeatsByComponent;
  const systemHealthAggregate = componentsShuffled.map(
    SystemHealthAggregateMapper,
  );
  const output_systemHealthAggregate = systemHealthAggregate;
  const output_users = inputs.users;
  return {
    components: output_components,
    heartbeatsByComponent: output_heartbeatsByComponent,
    systemHealthAggregate: output_systemHealthAggregate,
    users: output_users,
  };
}
