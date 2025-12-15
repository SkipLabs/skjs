export type UserId = string;

export type UserValue = {
  name: string;
  directRoleIds: Array<string>;
  groupIds: Array<string>;
};

export type User = UserValue & { id: UserId };

export type GroupId = string;

export type GroupValue = {
  name: string;
  parentGroupId: string | null;
  roleIds: Array<string>;
};

export type Group = GroupValue & { id: GroupId };

export type RoleId = string;

export type RoleValue = {
  name: string;
  permissionIds: Array<string>;
};

export type Role = RoleValue & { id: RoleId };

export type PermissionId = string;

export type PermissionValue = {
  name: string;
  resource: string;
  action: string;
};

export type Permission = PermissionValue & { id: PermissionId };

export type EffectivePermissionId = string;

export type EffectivePermissionValue = {
  userId: string;
  permissionId: string;
  permissionName: string;
  resource: string;
  action: string;
  sourceType: string;
  sourceId: string;
};

export type EffectivePermission = EffectivePermissionValue & { id: EffectivePermissionId };
