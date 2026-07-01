import { AclEntryByResourceMapper } from "./mappers/AclEntryByResourceMapper.js";
import { GroupMemberByGroupMapper } from "./mappers/GroupMemberByGroupMapper.js";
import { GroupMemberByUserFullMapper } from "./mappers/GroupMemberByUserFullMapper.js";
import type {
  AclEntry_skip_id_,
  AclEntry,
  AclEntry_skip_value_,
  GroupMember_skip_id_,
  GroupMember,
  GroupMember_skip_value_,
  Group_skip_id_,
  Group,
  Group_skip_value_,
  AclResource_skip_id_,
  AclResource,
  AclResource_skip_value_,
  Role_skip_id_,
  Role,
  Role_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ResourceIdKey,
  GroupIdKey,
  UserIdKey,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly aclEntries: EagerCollection<AclEntry_skip_id_, AclEntry_skip_value_>;
  readonly groupMembers: EagerCollection<
    GroupMember_skip_id_,
    GroupMember_skip_value_
  >;
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
  readonly resources: EagerCollection<
    AclResource_skip_id_,
    AclResource_skip_value_
  >;
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly aclEntries: EagerCollection<AclEntry_skip_id_, AclEntry_skip_value_>;
  readonly aclEntriesByResource: EagerCollection<ResourceIdKey, AclEntry>;
  readonly groupMembers: EagerCollection<
    GroupMember_skip_id_,
    GroupMember_skip_value_
  >;
  readonly groupMembersByGroup: EagerCollection<GroupIdKey, GroupMember>;
  readonly groupMembersByUser: EagerCollection<UserIdKey, GroupMember>;
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
  readonly resources: EagerCollection<
    AclResource_skip_id_,
    AclResource_skip_value_
  >;
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const aclEntriesByResource = inputs.aclEntries.map(AclEntryByResourceMapper);
  const groupMembersByGroup = inputs.groupMembers.map(GroupMemberByGroupMapper);
  const groupMembersByUser = inputs.groupMembers.map(
    GroupMemberByUserFullMapper,
  );
  const output_aclEntries = inputs.aclEntries;
  const output_aclEntriesByResource = aclEntriesByResource;
  const output_groupMembers = inputs.groupMembers;
  const output_groupMembersByGroup = groupMembersByGroup;
  const output_groupMembersByUser = groupMembersByUser;
  const output_groups = inputs.groups;
  const output_resources = inputs.resources;
  const output_roles = inputs.roles;
  const output_users = inputs.users;
  return {
    aclEntries: output_aclEntries,
    aclEntriesByResource: output_aclEntriesByResource,
    groupMembers: output_groupMembers,
    groupMembersByGroup: output_groupMembersByGroup,
    groupMembersByUser: output_groupMembersByUser,
    groups: output_groups,
    resources: output_resources,
    roles: output_roles,
    users: output_users,
  };
}
