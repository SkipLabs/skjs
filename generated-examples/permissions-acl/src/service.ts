import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { AclEntriesByResourceResource } from "./resources/AclEntriesByResourceResource.js";
import { GroupsResource } from "./resources/GroupsResource.js";
import { ListAclEntriesInternalResource } from "./resources/ListAclEntriesInternalResource.js";
import { ListGroupMembersInternalResource } from "./resources/ListGroupMembersInternalResource.js";
import { ListGroupMembersResource } from "./resources/ListGroupMembersResource.js";
import { ListUserGroupsResource } from "./resources/ListUserGroupsResource.js";
import { ResourcesResource } from "./resources/ResourcesResource.js";
import { RolesResource } from "./resources/RolesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  AclEntry_skip_id_,
  AclEntry_skip_value_,
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  Group_skip_id_,
  Group_skip_value_,
  AclResource_skip_id_,
  AclResource_skip_value_,
  Role_skip_id_,
  Role_skip_value_,
  User_skip_id_,
  User_skip_value_,
  AclEntry,
  GroupMember,
  Group,
  AclResource,
  Role,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly aclEntries: InputDefinition<AclEntry_skip_id_, AclEntry_skip_value_>;
  readonly groupMembers: InputDefinition<
    GroupMember_skip_id_,
    GroupMember_skip_value_
  >;
  readonly groups: InputDefinition<Group_skip_id_, Group_skip_value_>;
  readonly resources: InputDefinition<
    AclResource_skip_id_,
    AclResource_skip_value_
  >;
  readonly roles: InputDefinition<Role_skip_id_, Role_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly aclEntriesByResourceResource: ResourceClass<GraphCollections, Json>;
  readonly groupsResource: ResourceClass<GraphCollections, Json>;
  readonly listAclEntriesInternalResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listGroupMembersInternalResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listGroupMembersResource: ResourceClass<GraphCollections, Json>;
  readonly listUserGroupsResource: ResourceClass<GraphCollections, Json>;
  readonly resourcesResource: ResourceClass<GraphCollections, Json>;
  readonly rolesResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      aclEntries: new InputDefinition<AclEntry_skip_id_, AclEntry_skip_value_>(
        [],
      ),
      groupMembers: new InputDefinition<
        GroupMember_skip_id_,
        GroupMember_skip_value_
      >([]),
      groups: new InputDefinition<Group_skip_id_, Group_skip_value_>([]),
      resources: new InputDefinition<
        AclResource_skip_id_,
        AclResource_skip_value_
      >([]),
      roles: new InputDefinition<Role_skip_id_, Role_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      aclEntriesByResourceResource: AclEntriesByResourceResource,
      groupsResource: GroupsResource,
      listAclEntriesInternalResource: ListAclEntriesInternalResource,
      listGroupMembersInternalResource: ListGroupMembersInternalResource,
      listGroupMembersResource: ListGroupMembersResource,
      listUserGroupsResource: ListUserGroupsResource,
      resourcesResource: ResourcesResource,
      rolesResource: RolesResource,
      getMeResource: getMeResource,
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
