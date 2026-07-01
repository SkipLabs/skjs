import type { Json } from "@skipruntime/core";

export type AddMembershipRequest = {
  readonly role: MembershipRole;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type AddMembershipRequest_skip_id_ = {
  readonly role: MembershipRole;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type AddMembershipRequest_skip_value_ = {
  readonly role: MembershipRole;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type Channel = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly id: string;
  readonly name: string;
  readonly topic?: string;
  readonly updatedAt?: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type ChannelList = { readonly channels: Channel[] } & {
  readonly [key: string]: Json | null;
};

export type ChannelList_skip_id_ = { readonly channels: Channel[] } & {
  readonly [key: string]: Json | null;
};

export type ChannelList_skip_value_ = { readonly channels: Channel[] } & {
  readonly [key: string]: Json | null;
};

export type Channel_skip_id_ = string;

export type Channel_skip_value_ = {
  readonly createdAt: string;
  readonly createdBy: string;
  readonly name: string;
  readonly topic?: string;
  readonly updatedAt?: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type CreateChannelRequest = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type CreateChannelRequest_skip_id_ = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type CreateChannelRequest_skip_value_ = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type CreateMessageRequest = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreateMessageRequest_skip_id_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreateMessageRequest_skip_value_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type CreateWorkspaceRequest = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateWorkspaceRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateWorkspaceRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type GetChannelParams = { readonly channelId: string } & {
  readonly [key: string]: Json | null;
};

export type GetMessageParams = { readonly messageId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserByIdParams = { readonly targetUserId: string } & {
  readonly [key: string]: Json | null;
};

export type GetWorkspaceMemberParams = {
  readonly targetUserId: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type GetWorkspaceParams = { readonly workspaceId: string } & {
  readonly [key: string]: Json | null;
};

export type ListChannelMessagesParams = { readonly channelId: string } & {
  readonly [key: string]: Json | null;
};

export type ListMyWorkspacesParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListWorkspaceChannelsParams = { readonly workspaceId: string } & {
  readonly [key: string]: Json | null;
};

export type ListWorkspaceMembersParams = { readonly workspaceId: string } & {
  readonly [key: string]: Json | null;
};

export type Membership = {
  readonly joinedAt: string;
  readonly role: MembershipRole;
  readonly userId: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type MembershipKey = {
  readonly userId: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type MembershipList = { readonly memberships: Membership[] } & {
  readonly [key: string]: Json | null;
};

export type MembershipList_skip_id_ = { readonly memberships: Membership[] } & {
  readonly [key: string]: Json | null;
};

export type MembershipList_skip_value_ = {
  readonly memberships: Membership[];
} & { readonly [key: string]: Json | null };

export type MembershipRole = "OWNER" | "ADMIN" | "MEMBER";

export type MembershipRole_skip_id_ = "OWNER" | "ADMIN" | "MEMBER";

export type MembershipRole_skip_value_ = "OWNER" | "ADMIN" | "MEMBER";

export type Membership_skip_id_ = {
  readonly userId: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type Membership_skip_value_ = {
  readonly joinedAt: string;
  readonly role: MembershipRole;
} & { readonly [key: string]: Json | null };

export type Message = {
  readonly authorId: string;
  readonly body: string;
  readonly channelId: string;
  readonly createdAt: string;
  readonly editedAt?: string;
  readonly id: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type MessageList = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type MessageList_skip_id_ = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type MessageList_skip_value_ = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type Message_skip_id_ = string;

export type Message_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly channelId: string;
  readonly createdAt: string;
  readonly editedAt?: string;
  readonly workspaceId: string;
} & { readonly [key: string]: Json | null };

export type UpdateChannelRequest = {
  readonly name?: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type UpdateChannelRequest_skip_id_ = {
  readonly name?: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type UpdateChannelRequest_skip_value_ = {
  readonly name?: string;
  readonly topic?: string;
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

export type UpdateMembershipRequest = { readonly role: MembershipRole } & {
  readonly [key: string]: Json | null;
};

export type UpdateMembershipRequest_skip_id_ = {
  readonly role: MembershipRole;
} & { readonly [key: string]: Json | null };

export type UpdateMembershipRequest_skip_value_ = {
  readonly role: MembershipRole;
} & { readonly [key: string]: Json | null };

export type UpdateMessageRequest = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateMessageRequest_skip_id_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateMessageRequest_skip_value_ = { readonly body: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateWorkspaceRequest = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWorkspaceRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateWorkspaceRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
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

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
} & { readonly [key: string]: Json | null };

export type Workspace = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type WorkspaceList = { readonly workspaces: Workspace[] } & {
  readonly [key: string]: Json | null;
};

export type WorkspaceList_skip_id_ = { readonly workspaces: Workspace[] } & {
  readonly [key: string]: Json | null;
};

export type WorkspaceList_skip_value_ = { readonly workspaces: Workspace[] } & {
  readonly [key: string]: Json | null;
};

export type Workspace_skip_id_ = string;

export type Workspace_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };
