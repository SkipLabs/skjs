import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetChannelResource } from "./resources/GetChannelResource.js";
import { GetMembershipResource } from "./resources/GetMembershipResource.js";
import { GetMessageResource } from "./resources/GetMessageResource.js";
import { GetWorkspaceResource } from "./resources/GetWorkspaceResource.js";
import { ListChannelMessagesResource } from "./resources/ListChannelMessagesResource.js";
import { ListMyWorkspacesResource } from "./resources/ListMyWorkspacesResource.js";
import { ListWorkspaceChannelsResource } from "./resources/ListWorkspaceChannelsResource.js";
import { ListWorkspaceMembersResource } from "./resources/ListWorkspaceMembersResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Channel_skip_id_,
  Channel_skip_value_,
  MembershipKey,
  Membership_skip_value_,
  Message_skip_id_,
  Message_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Workspace_skip_id_,
  Workspace_skip_value_,
  ListMyWorkspacesParams,
  Channel,
  Membership,
  Message,
  User,
  Workspace,
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
  readonly channels: InputDefinition<Channel_skip_id_, Channel_skip_value_>;
  readonly memberships: InputDefinition<MembershipKey, Membership_skip_value_>;
  readonly messages: InputDefinition<Message_skip_id_, Message_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly workspaces: InputDefinition<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getChannelResource: ResourceClass<GraphCollections, Json>;
  readonly getMembershipResource: ResourceClass<GraphCollections, Json>;
  readonly getMessageResource: ResourceClass<GraphCollections, Json>;
  readonly getWorkspaceResource: ResourceClass<GraphCollections, Json>;
  readonly listChannelMessagesResource: ResourceClass<GraphCollections, Json>;
  readonly listMyWorkspacesResource: ResourceClass<
    GraphCollections,
    ListMyWorkspacesParams
  >;
  readonly listWorkspaceChannelsResource: ResourceClass<GraphCollections, Json>;
  readonly listWorkspaceMembersResource: ResourceClass<GraphCollections, Json>;
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
      channels: new InputDefinition<Channel_skip_id_, Channel_skip_value_>([]),
      memberships: new InputDefinition<MembershipKey, Membership_skip_value_>(
        [],
      ),
      messages: new InputDefinition<Message_skip_id_, Message_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      workspaces: new InputDefinition<
        Workspace_skip_id_,
        Workspace_skip_value_
      >([]),
    };
    this.resources = {
      getChannelResource: GetChannelResource,
      getMembershipResource: GetMembershipResource,
      getMessageResource: GetMessageResource,
      getWorkspaceResource: GetWorkspaceResource,
      listChannelMessagesResource: ListChannelMessagesResource,
      listMyWorkspacesResource: ListMyWorkspacesResource,
      listWorkspaceChannelsResource: ListWorkspaceChannelsResource,
      listWorkspaceMembersResource: ListWorkspaceMembersResource,
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
