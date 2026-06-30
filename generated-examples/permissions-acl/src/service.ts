import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetGroupResource } from "./resources/GetGroupResource.js";
import { GetResourceResource } from "./resources/GetResourceResource.js";
import { GetRoleBindingResource } from "./resources/GetRoleBindingResource.js";
import { GetRoleResource } from "./resources/GetRoleResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { GroupMembershipsByGroupResource } from "./resources/GroupMembershipsByGroupResource.js";
import { GroupMembershipsByUserResource } from "./resources/GroupMembershipsByUserResource.js";
import { ListGroupMembersResource } from "./resources/ListGroupMembersResource.js";
import { ListGroupMembershipsRawResource } from "./resources/ListGroupMembershipsRawResource.js";
import { ListGroupsResource } from "./resources/ListGroupsResource.js";
import { ListResourcesResource } from "./resources/ListResourcesResource.js";
import { ListRoleBindingsResource } from "./resources/ListRoleBindingsResource.js";
import { RoleBindingsByResourceResource } from "./resources/RoleBindingsByResourceResource.js";
import { RoleBindingsByRoleResource } from "./resources/RoleBindingsByRoleResource.js";
import type {
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  Group_skip_id_,
  Group_skip_value_,
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_,
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  Role_skip_id_,
  Role_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListGroupMembersParams,
  ListGroupsParams,
  ListResourcesParams,
  ListRoleBindingsParams,
  GroupMembership,
  Group,
  ProtectedResource,
  RoleBinding,
  Role,
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
  readonly groupMemberships: InputDefinition<
    GroupMembership_skip_id_,
    GroupMembership_skip_value_
  >;
  readonly groups: InputDefinition<Group_skip_id_, Group_skip_value_>;
  readonly resources: InputDefinition<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  >;
  readonly roleBindings: InputDefinition<
    RoleBinding_skip_id_,
    RoleBinding_skip_value_
  >;
  readonly roles: InputDefinition<Role_skip_id_, Role_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getGroupResource: ResourceClass<GraphCollections, Json>;
  readonly getResourceResource: ResourceClass<GraphCollections, Json>;
  readonly getRoleBindingResource: ResourceClass<GraphCollections, Json>;
  readonly getRoleResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, Json>;
  readonly groupMembershipsByGroupResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly groupMembershipsByUserResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listGroupMembersResource: ResourceClass<
    GraphCollections,
    ListGroupMembersParams
  >;
  readonly listGroupMembershipsRawResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listGroupsResource: ResourceClass<
    GraphCollections,
    ListGroupsParams
  >;
  readonly listResourcesResource: ResourceClass<
    GraphCollections,
    ListResourcesParams
  >;
  readonly listRoleBindingsResource: ResourceClass<
    GraphCollections,
    ListRoleBindingsParams
  >;
  readonly roleBindingsByResourceResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly roleBindingsByRoleResource: ResourceClass<GraphCollections, Json>;
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
      groupMemberships: new InputDefinition<
        GroupMembership_skip_id_,
        GroupMembership_skip_value_
      >([]),
      groups: new InputDefinition<Group_skip_id_, Group_skip_value_>([]),
      resources: new InputDefinition<
        ProtectedResource_skip_id_,
        ProtectedResource_skip_value_
      >([]),
      roleBindings: new InputDefinition<
        RoleBinding_skip_id_,
        RoleBinding_skip_value_
      >([]),
      roles: new InputDefinition<Role_skip_id_, Role_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getGroupResource: GetGroupResource,
      getResourceResource: GetResourceResource,
      getRoleBindingResource: GetRoleBindingResource,
      getRoleResource: GetRoleResource,
      getUserResource: GetUserResource,
      groupMembershipsByGroupResource: GroupMembershipsByGroupResource,
      groupMembershipsByUserResource: GroupMembershipsByUserResource,
      listGroupMembersResource: ListGroupMembersResource,
      listGroupMembershipsRawResource: ListGroupMembershipsRawResource,
      listGroupsResource: ListGroupsResource,
      listResourcesResource: ListResourcesResource,
      listRoleBindingsResource: ListRoleBindingsResource,
      roleBindingsByResourceResource: RoleBindingsByResourceResource,
      roleBindingsByRoleResource: RoleBindingsByRoleResource,
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
