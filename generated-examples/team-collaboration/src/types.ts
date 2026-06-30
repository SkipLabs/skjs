export type AddMemberRequest = {
  readonly role: MembershipRole;
  readonly userId: string;
};

export type AddMemberRequest_skip_id_ = {
  readonly role: MembershipRole;
  readonly userId: string;
};

export type AddMemberRequest_skip_value_ = {
  readonly role: MembershipRole;
  readonly userId: string;
};

export type ApiError = { readonly code?: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
};

export type Channel = {
  readonly createdAt: string;
  readonly createdById: string;
  readonly id: string;
  readonly name: string;
  readonly topic?: string;
  readonly updatedAt: string;
  readonly workspaceId: string;
};

export type ChannelIdParams = { readonly channelId: string };

export type ChannelList = { readonly channels: Channel[] };

export type ChannelList_skip_id_ = { readonly channels: Channel[] };

export type ChannelList_skip_value_ = { readonly channels: Channel[] };

export type Channel_skip_id_ = string;

export type Channel_skip_value_ = {
  readonly createdAt: string;
  readonly createdById: string;
  readonly name: string;
  readonly topic?: string;
  readonly updatedAt: string;
  readonly workspaceId: string;
};

export type CreateChannelRequest = {
  readonly name: string;
  readonly topic?: string;
};

export type CreateChannelRequest_skip_id_ = {
  readonly name: string;
  readonly topic?: string;
};

export type CreateChannelRequest_skip_value_ = {
  readonly name: string;
  readonly topic?: string;
};

export type CreateMessageRequest = { readonly body: string };

export type CreateMessageRequest_skip_id_ = { readonly body: string };

export type CreateMessageRequest_skip_value_ = { readonly body: string };

export type CreateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title: string;
};

export type CreateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title: string;
};

export type CreateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title: string;
};

export type CreateWorkspaceRequest = {
  readonly description?: string;
  readonly name: string;
};

export type CreateWorkspaceRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateWorkspaceRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
};

export type GetUserByIdParams = { readonly userId: string };

export type ListMyWorkspacesParams = { readonly authUserId: string };

export type Membership = {
  readonly joinedAt: string;
  readonly role: MembershipRole;
  readonly userId: string;
  readonly workspaceId: string;
};

export type MembershipKey = {
  readonly userId: string;
  readonly workspaceId: string;
};

export type MembershipKeyParams = {
  readonly userId: string;
  readonly workspaceId: string;
};

export type MembershipList = { readonly members: Membership[] };

export type MembershipList_skip_id_ = { readonly members: Membership[] };

export type MembershipList_skip_value_ = { readonly members: Membership[] };

export type MembershipRole = "OWNER" | "ADMIN" | "MEMBER";

export type MembershipRole_skip_id_ = "OWNER" | "ADMIN" | "MEMBER";

export type MembershipRole_skip_value_ = "OWNER" | "ADMIN" | "MEMBER";

export type Membership_skip_id_ = {
  readonly userId: string;
  readonly workspaceId: string;
};

export type Membership_skip_value_ = {
  readonly joinedAt: string;
  readonly role: MembershipRole;
};

export type Message = {
  readonly authorId: string;
  readonly body: string;
  readonly channelId: string;
  readonly createdAt: string;
  readonly editedAt?: string;
  readonly id: string;
  readonly workspaceId: string;
};

export type MessageIdParams = { readonly messageId: string };

export type MessageList = { readonly messages: Message[] };

export type MessageList_skip_id_ = { readonly messages: Message[] };

export type MessageList_skip_value_ = { readonly messages: Message[] };

export type Message_skip_id_ = string;

export type Message_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly channelId: string;
  readonly createdAt: string;
  readonly editedAt?: string;
  readonly workspaceId: string;
};

export type Task = {
  readonly assigneeId?: string;
  readonly createdAt: string;
  readonly createdById: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly id: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
  readonly workspaceId: string;
};

export type TaskIdParams = { readonly taskId: string };

export type TaskList = { readonly tasks: Task[] };

export type TaskList_skip_id_ = { readonly tasks: Task[] };

export type TaskList_skip_value_ = { readonly tasks: Task[] };

export type TaskStatus = "TODO" | "IN_PROGRESS" | "DONE" | "CANCELLED";

export type TaskStatus_skip_id_ = "TODO" | "IN_PROGRESS" | "DONE" | "CANCELLED";

export type TaskStatus_skip_value_ =
  | "TODO"
  | "IN_PROGRESS"
  | "DONE"
  | "CANCELLED";

export type Task_skip_id_ = string;

export type Task_skip_value_ = {
  readonly assigneeId?: string;
  readonly createdAt: string;
  readonly createdById: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status: TaskStatus;
  readonly title: string;
  readonly updatedAt: string;
  readonly workspaceId: string;
};

export type UpdateChannelRequest = {
  readonly name?: string;
  readonly topic?: string;
};

export type UpdateChannelRequest_skip_id_ = {
  readonly name?: string;
  readonly topic?: string;
};

export type UpdateChannelRequest_skip_value_ = {
  readonly name?: string;
  readonly topic?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly username?: string;
};

export type UpdateMembershipRequest = { readonly role: MembershipRole };

export type UpdateMembershipRequest_skip_id_ = {
  readonly role: MembershipRole;
};

export type UpdateMembershipRequest_skip_value_ = {
  readonly role: MembershipRole;
};

export type UpdateMessageRequest = { readonly body: string };

export type UpdateMessageRequest_skip_id_ = { readonly body: string };

export type UpdateMessageRequest_skip_value_ = { readonly body: string };

export type UpdateTaskRequest = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type UpdateTaskRequest_skip_id_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type UpdateTaskRequest_skip_value_ = {
  readonly assigneeId?: string;
  readonly description?: string;
  readonly dueAt?: string;
  readonly status?: TaskStatus;
  readonly title?: string;
};

export type UpdateWorkspaceRequest = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateWorkspaceRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateWorkspaceRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt?: string;
  readonly username?: string;
};

export type Workspace = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};

export type WorkspaceIdParams = { readonly workspaceId: string };

export type WorkspaceList = { readonly workspaces: Workspace[] };

export type WorkspaceList_skip_id_ = { readonly workspaces: Workspace[] };

export type WorkspaceList_skip_value_ = { readonly workspaces: Workspace[] };

export type Workspace_skip_id_ = string;

export type Workspace_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};
