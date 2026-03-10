import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

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


export type Inputs = {
  workspaces: InputDefinition<WorkspaceId, WorkspaceValue>;
  teams: InputDefinition<TeamId, TeamValue>;
  members: InputDefinition<MemberId, MemberValue>;
  channels: InputDefinition<ChannelId, ChannelValue>;
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

export type Resources = {
  readonly "workspaces": ResourceClass<GraphCollections, {}>;
  readonly "workspaces-teams": ResourceClass<GraphCollections, WorkspacesTeamsResourceParams>;
  readonly "workspaces-members": ResourceClass<GraphCollections, WorkspacesMembersResourceParams>;
  readonly "workspaces-channels": ResourceClass<GraphCollections, WorkspacesChannelsResourceParams>;
  readonly "teams-members": ResourceClass<GraphCollections, TeamsMembersResourceParams>;
  readonly "teams-channels": ResourceClass<GraphCollections, TeamsChannelsResourceParams>;
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
    for (const v of values) {
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
    for (const v of values) {
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
    for (const v of values) {
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
    for (const v of values) {
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
    for (const v of values) {
      if (v.teamId === this.teamId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class WorkspacesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
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

  constructor(params: WorkspacesTeamsResourceParams) {
    this.workspaceId = params.workspaceId;
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

  constructor(params: WorkspacesMembersResourceParams) {
    this.workspaceId = params.workspaceId;
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

  constructor(params: WorkspacesChannelsResourceParams) {
    this.workspaceId = params.workspaceId;
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

  constructor(params: TeamsMembersResourceParams) {
    this.teamId = params.teamId;
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

  constructor(params: TeamsChannelsResourceParams) {
    this.teamId = params.teamId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ChannelId, ChannelValue> {
    return cs.channels.map(FilterChannelsByTeamMapper, this.teamId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                    this.inputs = { workspaces: new InputDefinition<WorkspaceId, WorkspaceValue>([]), teams: new InputDefinition<TeamId, TeamValue>([]), members: new InputDefinition<MemberId, MemberValue>([]), channels: new InputDefinition<ChannelId, ChannelValue>([]) };
    this.resources = { "workspaces": WorkspacesResource, "workspaces-teams": WorkspacesTeamsResource, "workspaces-members": WorkspacesMembersResource, "workspaces-channels": WorkspacesChannelsResource, "teams-members": TeamsMembersResource, "teams-channels": TeamsChannelsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { workspaces: inputs.workspaces, teams: inputs.teams, members: inputs.members, channels: inputs.channels };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
