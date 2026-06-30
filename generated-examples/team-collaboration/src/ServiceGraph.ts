import type {
  Channel_skip_id_,
  Channel,
  Channel_skip_value_,
  MembershipKey,
  Membership_skip_value_,
  Membership,
  Message_skip_id_,
  Message,
  Message_skip_value_,
  Task_skip_id_,
  Task,
  Task_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  Workspace_skip_id_,
  Workspace,
  Workspace_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly channels: EagerCollection<Channel_skip_id_, Channel_skip_value_>;
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly workspaces: EagerCollection<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

export interface GraphCollections extends SharedCollections {
  readonly channels: EagerCollection<Channel_skip_id_, Channel_skip_value_>;
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
  readonly messages: EagerCollection<Message_skip_id_, Message_skip_value_>;
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly workspaces: EagerCollection<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_channels = inputs.channels;
  const output_memberships = inputs.memberships;
  const output_messages = inputs.messages;
  const output_tasks = inputs.tasks;
  const output_users = inputs.users;
  const output_workspaces = inputs.workspaces;
  return {
    channels: output_channels,
    memberships: output_memberships,
    messages: output_messages,
    tasks: output_tasks,
    users: output_users,
    workspaces: output_workspaces,
  };
}
