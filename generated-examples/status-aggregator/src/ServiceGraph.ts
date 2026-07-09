import { ComponentToStatusCountMapper } from "./mappers/ComponentToStatusCountMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Component_skip_id_,
  Component,
  Component_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ComponentStatusKey,
  ComponentStatusCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly components: EagerCollection<
    Component_skip_id_,
    Component_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly componentStatusCounts: EagerCollection<
    ComponentStatusKey,
    ComponentStatusCount
  >;
  readonly components: EagerCollection<
    Component_skip_id_,
    Component_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const componentStatusCounts = inputs.components.map(
    ComponentToStatusCountMapper,
  );
  const output_componentStatusCounts = componentStatusCounts.reduce(SumReducer);
  const output_components = inputs.components;
  const output_users = inputs.users;
  return {
    componentStatusCounts: output_componentStatusCounts,
    components: output_components,
    users: output_users,
  };
}
