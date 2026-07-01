import { FollowByFollowerMapper } from "./mappers/FollowByFollowerMapper.js";
import type {
  Activity_skip_id_,
  Activity,
  Activity_skip_value_,
  Follow_skip_id_,
  Follow,
  Follow_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  FollowByFollowerValue,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
  readonly follows: EagerCollection<Follow_skip_id_, Follow_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
  readonly follows: EagerCollection<Follow_skip_id_, Follow_skip_value_>;
  readonly followsByFollower: EagerCollection<
    User_skip_id_,
    FollowByFollowerValue
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const followsByFollower = inputs.follows.map(FollowByFollowerMapper);
  const output_activities = inputs.activities;
  const output_follows = inputs.follows;
  const output_followsByFollower = followsByFollower;
  const output_users = inputs.users;
  return {
    activities: output_activities,
    follows: output_follows,
    followsByFollower: output_followsByFollower,
    users: output_users,
  };
}
