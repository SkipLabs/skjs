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
  WorkspaceId,
  WorkspaceValue,
  TeamId,
  TeamValue,
  MemberId,
  MemberValue,
  ChannelId,
  ChannelValue,
  WorkspacesTeamsResourceParams,
  WorkspacesMembersResourceParams,
  WorkspacesChannelsResourceParams,
  TeamsMembersResourceParams,
  TeamsChannelsResourceParams,
} from "./types.js";


type Inputs = {
  workspaces: Entry<WorkspaceId, WorkspaceValue>[];
  teams: Entry<TeamId, TeamValue>[];
  members: Entry<MemberId, MemberValue>[];
  channels: Entry<ChannelId, ChannelValue>[];
};

export type InputCollections = {
  workspaces: EagerCollection<WorkspaceId, WorkspaceValue>;
  teams: EagerCollection<TeamId, TeamValue>;
  members: EagerCollection<MemberId, MemberValue>;
  channels: EagerCollection<ChannelId, ChannelValue>;
};

export type GraphCollections = {
  workspaces: EagerCollection<WorkspaceId, WorkspaceValue>;
  teams: EagerCollection<TeamId, TeamValue>;
  members: EagerCollection<MemberId, MemberValue>;
  channels: EagerCollection<ChannelId, ChannelValue>;
};

type Resources = {
  "workspaces": new (params: Json) => Resource<GraphCollections>;
  "workspaces-teams": new (params: Json) => Resource<GraphCollections>;
  "workspaces-members": new (params: Json) => Resource<GraphCollections>;
  "workspaces-channels": new (params: Json) => Resource<GraphCollections>;
  "teams-members": new (params: Json) => Resource<GraphCollections>;
  "teams-channels": new (params: Json) => Resource<GraphCollections>;
};

export class FilterTeamsByWorkspaceMapper implements Mapper<TeamId, TeamValue, TeamId, TeamValue> {
  private workspaceId: string;

  constructor(workspaceId: string) {
    this.workspaceId = workspaceId;
  }

  mapEntry(
    key: TeamId,
    values: Values<TeamValue>,
    _context: Context
  ): Iterable<[TeamId, TeamValue]> {
    const result: Array<[TeamId, TeamValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.workspaceId === this.workspaceId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterMembersByWorkspaceMapper implements Mapper<MemberId, MemberValue, MemberId, MemberValue> {
  private workspaceId: string;

  constructor(workspaceId: string) {
    this.workspaceId = workspaceId;
  }

  mapEntry(
    key: MemberId,
    values: Values<MemberValue>,
    _context: Context
  ): Iterable<[MemberId, MemberValue]> {
    const result: Array<[MemberId, MemberValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.workspaceId === this.workspaceId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterChannelsByWorkspaceMapper implements Mapper<ChannelId, ChannelValue, ChannelId, ChannelValue> {
  private workspaceId: string;

  constructor(workspaceId: string) {
    this.workspaceId = workspaceId;
  }

  mapEntry(
    key: ChannelId,
    values: Values<ChannelValue>,
    _context: Context
  ): Iterable<[ChannelId, ChannelValue]> {
    const result: Array<[ChannelId, ChannelValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.workspaceId === this.workspaceId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterMembersByTeamMapper implements Mapper<MemberId, MemberValue, MemberId, MemberValue> {
  private teamId: string;

  constructor(teamId: string) {
    this.teamId = teamId;
  }

  mapEntry(
    key: MemberId,
    values: Values<MemberValue>,
    _context: Context
  ): Iterable<[MemberId, MemberValue]> {
    const result: Array<[MemberId, MemberValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.teamId === this.teamId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterChannelsByTeamMapper implements Mapper<ChannelId, ChannelValue, ChannelId, ChannelValue> {
  private teamId: string;

  constructor(teamId: string) {
    this.teamId = teamId;
  }

  mapEntry(
    key: ChannelId,
    values: Values<ChannelValue>,
    _context: Context
  ): Iterable<[ChannelId, ChannelValue]> {
    const result: Array<[ChannelId, ChannelValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.teamId === this.teamId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class WorkspacesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<WorkspaceId, WorkspaceValue> {
    return cs.workspaces;
  }
}

export class WorkspacesTeamsResource implements Resource<GraphCollections> {
  private workspaceId: string;

  constructor(params: Json) {
    const typed = params as WorkspacesTeamsResourceParams;
    this.workspaceId = typed.workspaceId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TeamId, TeamValue> {
    return cs.teams.map(FilterTeamsByWorkspaceMapper, this.workspaceId);
  }
}

export class WorkspacesMembersResource implements Resource<GraphCollections> {
  private workspaceId: string;

  constructor(params: Json) {
    const typed = params as WorkspacesMembersResourceParams;
    this.workspaceId = typed.workspaceId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<MemberId, MemberValue> {
    return cs.members.map(FilterMembersByWorkspaceMapper, this.workspaceId);
  }
}

export class WorkspacesChannelsResource implements Resource<GraphCollections> {
  private workspaceId: string;

  constructor(params: Json) {
    const typed = params as WorkspacesChannelsResourceParams;
    this.workspaceId = typed.workspaceId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ChannelId, ChannelValue> {
    return cs.channels.map(FilterChannelsByWorkspaceMapper, this.workspaceId);
  }
}

export class TeamsMembersResource implements Resource<GraphCollections> {
  private teamId: string;

  constructor(params: Json) {
    const typed = params as TeamsMembersResourceParams;
    this.teamId = typed.teamId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<MemberId, MemberValue> {
    return cs.members.map(FilterMembersByTeamMapper, this.teamId);
  }
}

export class TeamsChannelsResource implements Resource<GraphCollections> {
  private teamId: string;

  constructor(params: Json) {
    const typed = params as TeamsChannelsResourceParams;
    this.teamId = typed.teamId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ChannelId, ChannelValue> {
    return cs.channels.map(FilterChannelsByTeamMapper, this.teamId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyWorkspaces: Entry<WorkspaceId, WorkspaceValue>[] = Array.of();
    const emptyTeams: Entry<TeamId, TeamValue>[] = Array.of();
    const emptyMembers: Entry<MemberId, MemberValue>[] = Array.of();
    const emptyChannels: Entry<ChannelId, ChannelValue>[] = Array.of();
    this.initialData = { workspaces: emptyWorkspaces, teams: emptyTeams, members: emptyMembers, channels: emptyChannels };
    this.resources = { "workspaces": WorkspacesResource, "workspaces-teams": WorkspacesTeamsResource, "workspaces-members": WorkspacesMembersResource, "workspaces-channels": WorkspacesChannelsResource, "teams-members": TeamsMembersResource, "teams-channels": TeamsChannelsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { workspaces: inputs.workspaces, teams: inputs.teams, members: inputs.members, channels: inputs.channels };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
