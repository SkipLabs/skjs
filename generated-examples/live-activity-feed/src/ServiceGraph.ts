import type {
  Activity_skip_id_,
  Activity,
  Activity_skip_value_,
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
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_activities = inputs.activities;
  const output_users = inputs.users;
  return { activities: output_activities, users: output_users };
}
