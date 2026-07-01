export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateGroupRequest = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
};

export type CreateGroupRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
};

export type CreateGroupRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
};

export type CreateResourceRequest = {
  readonly kind?: string;
  readonly name: string;
  readonly parentResourceId?: string;
};

export type CreateResourceRequest_skip_id_ = {
  readonly kind?: string;
  readonly name: string;
  readonly parentResourceId?: string;
};

export type CreateResourceRequest_skip_value_ = {
  readonly kind?: string;
  readonly name: string;
  readonly parentResourceId?: string;
};

export type CreateRoleBindingRequest = {
  readonly groupId?: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type CreateRoleBindingRequest_skip_id_ = {
  readonly groupId?: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type CreateRoleBindingRequest_skip_value_ = {
  readonly groupId?: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type CreateRoleRequest = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
};

export type CreateRoleRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
};

export type CreateRoleRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
};

export type EffectivePermissionSource = {
  readonly groupId?: string;
  readonly inherited: boolean;
  readonly resourceId: string;
  readonly roleBindingId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type EffectivePermissionSource_skip_id_ = {
  readonly groupId?: string;
  readonly inherited: boolean;
  readonly resourceId: string;
  readonly roleBindingId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type EffectivePermissionSource_skip_value_ = {
  readonly groupId?: string;
  readonly inherited: boolean;
  readonly resourceId: string;
  readonly roleBindingId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type EffectivePermissions = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectivePermissionSource[];
  readonly userId: string;
};

export type EffectivePermissionsKey = {
  readonly resourceId: string;
  readonly userId: string;
};

export type EffectivePermissions_skip_id_ = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectivePermissionSource[];
  readonly userId: string;
};

export type EffectivePermissions_skip_value_ = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectivePermissionSource[];
  readonly userId: string;
};

export type GetGroupParams = { readonly groupId: string };

export type GetResourceParams = { readonly resourceId: string };

export type GetRoleBindingParams = { readonly roleBindingId: string };

export type GetRoleParams = { readonly roleId: string };

export type GetUserParams = { readonly userId: string };

export type Group = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentGroupId?: string;
};

export type GroupIdKey = string;

export type GroupMembership = {
  readonly addedAt: string;
  readonly groupId: string;
  readonly userId: string;
};

export type GroupMembershipByGroupValue = {
  readonly addedAt: string;
  readonly userId: string;
};

export type GroupMembershipByUserValue = {
  readonly addedAt: string;
  readonly groupId: string;
};

export type GroupMembership_skip_id_ = {
  readonly groupId: string;
  readonly userId: string;
};

export type GroupMembership_skip_value_ = { readonly addedAt: string };

export type Group_skip_id_ = string;

export type Group_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentGroupId?: string;
};

export type ListEffectiveGroupsParams = { readonly userId: string };

export type ListGroupMembersParams = { readonly groupId: string };

export type ListGroupsParams = { readonly parentGroupId?: string };

export type ListResourcesParams = { readonly parentResourceId?: string };

export type ListRoleBindingsParams = {
  readonly groupId?: string;
  readonly resourceId?: string;
  readonly roleId?: string;
  readonly userId?: string;
};

export type PermissionCheckResult = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
};

export type PermissionCheckResult_skip_id_ = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
};

export type PermissionCheckResult_skip_value_ = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
};

export type ProtectedResource = {
  readonly createdAt: string;
  readonly id: string;
  readonly kind?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentResourceId?: string;
};

export type ProtectedResource_skip_id_ = string;

export type ProtectedResource_skip_value_ = {
  readonly createdAt: string;
  readonly kind?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentResourceId?: string;
};

export type ResourceIdKey = string;

export type Role = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly permissions: string[];
};

export type RoleBinding = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly groupId?: string;
  readonly id: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type RoleBindingByResourceValue = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly groupId?: string;
  readonly id: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type RoleBindingByRoleValue = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly groupId?: string;
  readonly id: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type RoleBinding_skip_id_ = string;

export type RoleBinding_skip_value_ = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly groupId?: string;
  readonly resourceId: string;
  readonly roleId: string;
  readonly userId?: string;
};

export type RoleIdKey = string;

export type Role_skip_id_ = string;

export type Role_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly permissions: string[];
};

export type UpdateGroupRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
};

export type UpdateGroupRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
};

export type UpdateGroupRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateResourceRequest = {
  readonly kind?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
};

export type UpdateResourceRequest_skip_id_ = {
  readonly kind?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
};

export type UpdateResourceRequest_skip_value_ = {
  readonly kind?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
};

export type UpdateRoleRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
};

export type UpdateRoleRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
};

export type UpdateRoleRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
};

export type UserIdKey = string;

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};
