import type { Json } from "@skipruntime/core";

export type AclEntry = {
  readonly grantedAt: string;
  readonly grantedBy: string;
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type AclEntryCompositeKey = {
  readonly principalId: string;
  readonly principalType: string;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type AclEntry_skip_id_ = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type AclEntry_skip_value_ = {
  readonly grantedAt: string;
  readonly grantedBy: string;
} & { readonly [key: string]: Json | null };

export type AclResource = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type AclResource_skip_id_ = string;

export type AclResource_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CheckPermissionParams = {
  readonly permission: string;
  readonly resourceId: string;
  readonly targetUserId: string;
} & { readonly [key: string]: Json | null };

export type CreateAclEntryRequest = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type CreateAclEntryRequest_skip_id_ = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type CreateAclEntryRequest_skip_value_ = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type CreateGroupRequest = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type CreateGroupRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type CreateGroupRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type CreateResourceRequest = {
  readonly description?: string;
  readonly name: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type CreateResourceRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type CreateResourceRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type CreateRoleRequest = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
} & { readonly [key: string]: Json | null };

export type CreateRoleRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
} & { readonly [key: string]: Json | null };

export type CreateRoleRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
  readonly permissions: string[];
} & { readonly [key: string]: Json | null };

export type EffectiveRights = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectiveRightsSource[];
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRightsParams = {
  readonly resourceId: string;
  readonly targetUserId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRightsSource = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRightsSource_skip_id_ = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRightsSource_skip_value_ = {
  readonly principalId: string;
  readonly principalType: PrincipalType;
  readonly resourceId: string;
  readonly roleId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRights_skip_id_ = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectiveRightsSource[];
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type EffectiveRights_skip_value_ = {
  readonly permissions: string[];
  readonly resourceId: string;
  readonly sources: EffectiveRightsSource[];
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetAclEntryParams = Record<string, Json | null>;

export type Group = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type GroupIdKey = string;

export type GroupMember = {
  readonly addedAt: string;
  readonly groupId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GroupMember_skip_id_ = {
  readonly groupId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GroupMember_skip_value_ = { readonly addedAt: string } & {
  readonly [key: string]: Json | null;
};

export type Group_skip_id_ = string;

export type Group_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type ListAclEntriesParams = Record<string, Json | null>;

export type ListGroupMembersParams = Record<string, Json | null>;

export type ListGroupsParams = Record<string, Json | null>;

export type ListResourceAncestorsParams = Record<string, Json | null>;

export type ListResourcesParams = Record<string, Json | null>;

export type ListUserGroupsParams = Record<string, Json | null>;

export type ListUsersParams = Record<string, Json | null>;

export type PermissionCheckResult = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type PermissionCheckResult_skip_id_ = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type PermissionCheckResult_skip_value_ = {
  readonly allowed: boolean;
  readonly permission: string;
  readonly resourceId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type PrincipalType = "USER" | "GROUP";

export type PrincipalType_skip_id_ = "USER" | "GROUP";

export type PrincipalType_skip_value_ = "USER" | "GROUP";

export type ResourceAncestorNode = {
  readonly depth: number;
  readonly parentResourceId?: string;
  readonly resourceId: string;
} & { readonly [key: string]: Json | null };

export type ResourceAncestorNode_skip_id_ = {
  readonly depth: number;
  readonly parentResourceId?: string;
  readonly resourceId: string;
} & { readonly [key: string]: Json | null };

export type ResourceAncestorNode_skip_value_ = {
  readonly depth: number;
  readonly parentResourceId?: string;
  readonly resourceId: string;
} & { readonly [key: string]: Json | null };

export type ResourceIdKey = string;

export type Role = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly permissions: string[];
} & { readonly [key: string]: Json | null };

export type Role_skip_id_ = string;

export type Role_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly permissions: string[];
} & { readonly [key: string]: Json | null };

export type UpdateGroupRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateGroupRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateGroupRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentGroupId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UpdateResourceRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateResourceRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateResourceRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly parentResourceId?: string;
} & { readonly [key: string]: Json | null };

export type UpdateRoleRequest = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateRoleRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateRoleRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
  readonly permissions?: string[];
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type UserIdKey = string;

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };
