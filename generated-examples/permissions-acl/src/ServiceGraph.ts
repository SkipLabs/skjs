import { GroupMembershipByGroupMapper } from "./mappers/GroupMembershipByGroupMapper.js";
import { GroupMembershipByUserMapper } from "./mappers/GroupMembershipByUserMapper.js";
import { RoleBindingByResourceMapper } from "./mappers/RoleBindingByResourceMapper.js";
import { RoleBindingByRoleMapper } from "./mappers/RoleBindingByRoleMapper.js";
import type {
  GroupMembership_skip_id_,
  GroupMembership,
  GroupMembership_skip_value_,
  Group_skip_id_,
  Group,
  Group_skip_value_,
  ProtectedResource_skip_id_,
  ProtectedResource,
  ProtectedResource_skip_value_,
  RoleBinding_skip_id_,
  RoleBinding,
  RoleBinding_skip_value_,
  Role_skip_id_,
  Role,
  Role_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  GroupMembershipByGroupValue,
  GroupMembershipByUserValue,
  RoleBindingByResourceValue,
  RoleBindingByRoleValue,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly groupMemberships: EagerCollection<
    GroupMembership_skip_id_,
    GroupMembership_skip_value_
  >;
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
  readonly resources: EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  >;
  readonly roleBindings: EagerCollection<
    RoleBinding_skip_id_,
    RoleBinding_skip_value_
  >;
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly groupMemberships: EagerCollection<
    GroupMembership_skip_id_,
    GroupMembership_skip_value_
  >;
  readonly groupMembershipsByGroup: EagerCollection<
    Group_skip_id_,
    GroupMembershipByGroupValue
  >;
  readonly groupMembershipsByUser: EagerCollection<
    User_skip_id_,
    GroupMembershipByUserValue
  >;
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
  readonly resources: EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  >;
  readonly roleBindings: EagerCollection<
    RoleBinding_skip_id_,
    RoleBinding_skip_value_
  >;
  readonly roleBindingsByResource: EagerCollection<
    ProtectedResource_skip_id_,
    RoleBindingByResourceValue
  >;
  readonly roleBindingsByRole: EagerCollection<
    Role_skip_id_,
    RoleBindingByRoleValue
  >;
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const groupMembershipsByGroup = inputs.groupMemberships.map(
    GroupMembershipByGroupMapper,
  );
  const groupMembershipsByUser = inputs.groupMemberships.map(
    GroupMembershipByUserMapper,
  );
  const output_groupMemberships = inputs.groupMemberships;
  const output_groupMembershipsByGroup = groupMembershipsByGroup;
  const output_groupMembershipsByUser = groupMembershipsByUser;
  const output_groups = inputs.groups;
  const output_resources = inputs.resources;
  const output_roleBindings = inputs.roleBindings;
  const roleBindingsByResource = inputs.roleBindings.map(
    RoleBindingByResourceMapper,
  );
  const output_roleBindingsByResource = roleBindingsByResource;
  const roleBindingsByRole = inputs.roleBindings.map(RoleBindingByRoleMapper);
  const output_roleBindingsByRole = roleBindingsByRole;
  const output_roles = inputs.roles;
  const output_users = inputs.users;
  return {
    groupMemberships: output_groupMemberships,
    groupMembershipsByGroup: output_groupMembershipsByGroup,
    groupMembershipsByUser: output_groupMembershipsByUser,
    groups: output_groups,
    resources: output_resources,
    roleBindings: output_roleBindings,
    roleBindingsByResource: output_roleBindingsByResource,
    roleBindingsByRole: output_roleBindingsByRole,
    roles: output_roles,
    users: output_users,
  };
}
