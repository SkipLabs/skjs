import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { ChannelsByWorkspaceResource } from "./resources/ChannelsByWorkspaceResource.js";
import { GetChannelResource } from "./resources/GetChannelResource.js";
import { GetMembershipResource } from "./resources/GetMembershipResource.js";
import { GetMessageResource } from "./resources/GetMessageResource.js";
import { GetTaskResource } from "./resources/GetTaskResource.js";
import { GetUserResource } from "./resources/GetUserResource.js";
import { GetWorkspaceResource } from "./resources/GetWorkspaceResource.js";
import { MembershipsByUserResource } from "./resources/MembershipsByUserResource.js";
import { MembershipsByWorkspaceResource } from "./resources/MembershipsByWorkspaceResource.js";
import { MessagesByChannelResource } from "./resources/MessagesByChannelResource.js";
import { TasksByWorkspaceResource } from "./resources/TasksByWorkspaceResource.js";
import type {
  Channel_skip_id_,
  Channel_skip_value_,
  MembershipKey,
  Membership_skip_value_,
  Message_skip_id_,
  Message_skip_value_,
  Task_skip_id_,
  Task_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Workspace_skip_id_,
  Workspace_skip_value_,
  Channel,
  Membership,
  Message,
  Task,
  User,
  Workspace,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly channels: InputDefinition<Channel_skip_id_, Channel_skip_value_>;
  readonly memberships: InputDefinition<MembershipKey, Membership_skip_value_>;
  readonly messages: InputDefinition<Message_skip_id_, Message_skip_value_>;
  readonly tasks: InputDefinition<Task_skip_id_, Task_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly workspaces: InputDefinition<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly channelsByWorkspaceResource: ResourceClass<GraphCollections, Json>;
  readonly getChannelResource: ResourceClass<GraphCollections, Json>;
  readonly getMembershipResource: ResourceClass<GraphCollections, Json>;
  readonly getMessageResource: ResourceClass<GraphCollections, Json>;
  readonly getTaskResource: ResourceClass<GraphCollections, Json>;
  readonly getUserResource: ResourceClass<GraphCollections, Json>;
  readonly getWorkspaceResource: ResourceClass<GraphCollections, Json>;
  readonly membershipsByUserResource: ResourceClass<GraphCollections, Json>;
  readonly membershipsByWorkspaceResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly messagesByChannelResource: ResourceClass<GraphCollections, Json>;
  readonly tasksByWorkspaceResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      channels: new InputDefinition<Channel_skip_id_, Channel_skip_value_>([]),
      memberships: new InputDefinition<MembershipKey, Membership_skip_value_>(
        [],
      ),
      messages: new InputDefinition<Message_skip_id_, Message_skip_value_>([]),
      tasks: new InputDefinition<Task_skip_id_, Task_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      workspaces: new InputDefinition<
        Workspace_skip_id_,
        Workspace_skip_value_
      >([]),
    };
    this.resources = {
      channelsByWorkspaceResource: ChannelsByWorkspaceResource,
      getChannelResource: GetChannelResource,
      getMembershipResource: GetMembershipResource,
      getMessageResource: GetMessageResource,
      getTaskResource: GetTaskResource,
      getUserResource: GetUserResource,
      getWorkspaceResource: GetWorkspaceResource,
      membershipsByUserResource: MembershipsByUserResource,
      membershipsByWorkspaceResource: MembershipsByWorkspaceResource,
      messagesByChannelResource: MessagesByChannelResource,
      tasksByWorkspaceResource: TasksByWorkspaceResource,
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
