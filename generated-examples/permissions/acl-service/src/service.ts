import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "@skipruntime/core";

import type {
  UserId,
  UserValue,
  GroupId,
  GroupValue,
  RoleId,
  RoleValue,
  PermissionId,
  PermissionValue,
  EffectivePermissionId,
  EffectivePermissionValue,
} from "./types.js";

export type RoleAssignmentValue = {
  userId: string;
  roleId: string;
  sourceType: string;
  sourceId: string;
};

type Inputs = {
  users: Entry<UserId, UserValue>[];
  groups: Entry<GroupId, GroupValue>[];
  roles: Entry<RoleId, RoleValue>[];
  permissions: Entry<PermissionId, PermissionValue>[];
};

export type InputCollections = {
  users: EagerCollection<UserId, UserValue>;
  groups: EagerCollection<GroupId, GroupValue>;
  roles: EagerCollection<RoleId, RoleValue>;
  permissions: EagerCollection<PermissionId, PermissionValue>;
};

export type GraphCollections = {
  users: EagerCollection<UserId, UserValue>;
  groups: EagerCollection<GroupId, GroupValue>;
  roles: EagerCollection<RoleId, RoleValue>;
  permissions: EagerCollection<PermissionId, PermissionValue>;
  effectivePermissions: EagerCollection<EffectivePermissionId, EffectivePermissionValue>;
};

type Resources = {
  "users": new (params: Json) => Resource<GraphCollections>;
  "groups": new (params: Json) => Resource<GraphCollections>;
  "roles": new (params: Json) => Resource<GraphCollections>;
  "permissions": new (params: Json) => Resource<GraphCollections>;
  "effectivePermissions": new (params: Json) => Resource<GraphCollections>;
};

export class UserToRoleAssignmentsMapper implements Mapper<UserId, UserValue, [string, string, string, string], RoleAssignmentValue> {
  private groups: EagerCollection<GroupId, GroupValue>;

  constructor(groups: EagerCollection<GroupId, GroupValue>) {
    this.groups = groups;
  }

  private collectAllGroupIds(groupIds: Array<string>, visited: Set<string>): void {
    for (let i = 0; i < groupIds.length; i++) {
      const groupId = groupIds[i]!;
      if (visited.has(groupId)) {
        continue;
      }
      visited.add(groupId);
      const groupValues = this.groups.getArray(groupId);
      if (groupValues.length > 0) {
        const group = groupValues[0]!;
        if (group.parentGroupId !== null) {
          this.collectAllGroupIds(Array.of(group.parentGroupId), visited);
        }
      }
    }
  }

  mapEntry(
    key: UserId,
    values: Values<UserValue>,
    _context: Context
  ): Iterable<[[string, string, string, string], RoleAssignmentValue]> {
    const arr = values.toArray();
    const result: Array<[[string, string, string, string], RoleAssignmentValue]> = Array.of();
    
    for (let i = 0; i < arr.length; i++) {
      const user = arr[i]!;
      const userId = key;
      
      for (let j = 0; j < user.directRoleIds.length; j++) {
        const roleId = user.directRoleIds[j]!;
        const compositeKey: [string, string, string, string] = [userId, roleId, "direct", userId];
        const assignment: RoleAssignmentValue = {
          userId: userId,
          roleId: roleId,
          sourceType: "direct",
          sourceId: userId
        };
        result.push([compositeKey, assignment]);
      }
      
      const allGroupIds = new Set<string>();
      this.collectAllGroupIds(user.groupIds, allGroupIds);
      
      const groupIdArray = Array.from(allGroupIds);
      for (let g = 0; g < groupIdArray.length; g++) {
        const groupId = groupIdArray[g]!;
        const groupValues = this.groups.getArray(groupId);
        if (groupValues.length > 0) {
          const group = groupValues[0]!;
          for (let r = 0; r < group.roleIds.length; r++) {
            const roleId = group.roleIds[r]!;
            const compositeKey: [string, string, string, string] = [userId, roleId, "group", groupId];
            const assignment: RoleAssignmentValue = {
              userId: userId,
              roleId: roleId,
              sourceType: "group",
              sourceId: groupId
            };
            result.push([compositeKey, assignment]);
          }
        }
      }
    }
    
    return result;
  }
}

export class RoleAssignmentToEffectivePermissionMapper implements Mapper<[string, string, string, string], RoleAssignmentValue, EffectivePermissionId, EffectivePermissionValue> {
  private roles: EagerCollection<RoleId, RoleValue>;
  private permissions: EagerCollection<PermissionId, PermissionValue>;

  constructor(roles: EagerCollection<RoleId, RoleValue>, permissions: EagerCollection<PermissionId, PermissionValue>) {
    this.roles = roles;
    this.permissions = permissions;
  }

  mapEntry(
    _key: [string, string, string, string],
    values: Values<RoleAssignmentValue>,
    _context: Context
  ): Iterable<[EffectivePermissionId, EffectivePermissionValue]> {
    const arr = values.toArray();
    const result: Array<[EffectivePermissionId, EffectivePermissionValue]> = Array.of();
    
    for (let i = 0; i < arr.length; i++) {
      const assignment = arr[i]!;
      const roleValues = this.roles.getArray(assignment.roleId);
      
      if (roleValues.length > 0) {
        const role = roleValues[0]!;
        
        for (let p = 0; p < role.permissionIds.length; p++) {
          const permissionId = role.permissionIds[p]!;
          const permissionValues = this.permissions.getArray(permissionId);
          
          if (permissionValues.length > 0) {
            const permission = permissionValues[0]!;
            const effectivePermissionId: EffectivePermissionId = JSON.stringify([assignment.userId, permissionId, assignment.sourceType, assignment.sourceId]);
            const effectivePermission: EffectivePermissionValue = {
              userId: assignment.userId,
              permissionId: permissionId,
              permissionName: permission.name,
              resource: permission.resource,
              action: permission.action,
              sourceType: assignment.sourceType,
              sourceId: assignment.sourceId
            };
            result.push([effectivePermissionId, effectivePermission]);
          }
        }
      }
    }
    
    return result;
  }
}

export class FilterByUserIdMapper implements Mapper<EffectivePermissionId, EffectivePermissionValue, EffectivePermissionId, EffectivePermissionValue> {
  private userId: string;

  constructor(userId: string) {
    this.userId = userId;
  }

  mapEntry(
    key: EffectivePermissionId,
    values: Values<EffectivePermissionValue>,
    _context: Context
  ): Iterable<[EffectivePermissionId, EffectivePermissionValue]> {
    const arr = values.toArray();
    const result: Array<[EffectivePermissionId, EffectivePermissionValue]> = Array.of();
    
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    
    return result;
  }
}

export class UsersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UserId, UserValue> {
    return cs.users;
  }
}

export class GroupsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<GroupId, GroupValue> {
    return cs.groups;
  }
}

export class RolesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RoleId, RoleValue> {
    return cs.roles;
  }
}

export class PermissionsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PermissionId, PermissionValue> {
    return cs.permissions;
  }
}

export class EffectivePermissionsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<EffectivePermissionId, EffectivePermissionValue> {
    return cs.effectivePermissions;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyUsers: Entry<UserId, UserValue>[] = Array.of();
    const emptyGroups: Entry<GroupId, GroupValue>[] = Array.of();
    const emptyRoles: Entry<RoleId, RoleValue>[] = Array.of();
    const emptyPermissions: Entry<PermissionId, PermissionValue>[] = Array.of();
    this.initialData = { users: emptyUsers, groups: emptyGroups, roles: emptyRoles, permissions: emptyPermissions };
    this.resources = { 
      "users": UsersResource, 
      "groups": GroupsResource, 
      "roles": RolesResource, 
      "permissions": PermissionsResource,
      "effectivePermissions": EffectivePermissionsResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const roleAssignments = inputs.users.map(UserToRoleAssignmentsMapper, inputs.groups);
    const effectivePermissions = roleAssignments.map(RoleAssignmentToEffectivePermissionMapper, inputs.roles, inputs.permissions);
    
    return {
      users: inputs.users,
      groups: inputs.groups,
      roles: inputs.roles,
      permissions: inputs.permissions,
      effectivePermissions: effectivePermissions
    };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
