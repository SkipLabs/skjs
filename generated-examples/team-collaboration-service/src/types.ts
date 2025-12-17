export type WorkspaceId = string;

export type WorkspaceValue = {
  name: string;
  description: string | null;
  ownerId: string;
  createdAt: number;
  memberCount: number;
};

export type Workspace = {
  id: WorkspaceId;
  name: string;
  description: string | null;
  ownerId: string;
  createdAt: number;
  memberCount: number;
};

export type TeamId = string;

export type TeamValue = {
  workspaceId: string;
  name: string;
  description: string | null;
  createdAt: number;
  memberCount: number;
};

export type Team = {
  id: TeamId;
  workspaceId: string;
  name: string;
  description: string | null;
  createdAt: number;
  memberCount: number;
};

export type MemberId = string;

export type MemberValue = {
  workspaceId: string;
  teamId: string | null;
  userId: string;
  role: string;
  joinedAt: number;
};

export type Member = {
  id: MemberId;
  workspaceId: string;
  teamId: string | null;
  userId: string;
  role: string;
  joinedAt: number;
};

export type ChannelId = string;

export type ChannelValue = {
  workspaceId: string;
  teamId: string | null;
  name: string;
  isPrivate: number;
  createdAt: number;
};

export type Channel = {
  id: ChannelId;
  workspaceId: string;
  teamId: string | null;
  name: string;
  isPrivate: number;
  createdAt: number;
};

export type WorkspacesTeamsResourceParams = {
  workspaceId: string;
};

export type WorkspacesMembersResourceParams = {
  workspaceId: string;
};

export type WorkspacesChannelsResourceParams = {
  workspaceId: string;
};

export type TeamsMembersResourceParams = {
  teamId: string;
};

export type TeamsChannelsResourceParams = {
  teamId: string;
};
