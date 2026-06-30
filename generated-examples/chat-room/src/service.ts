import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { CheckMembershipResource } from "./resources/CheckMembershipResource.js";
import { GetMessageResource } from "./resources/GetMessageResource.js";
import { ListRoomMembersResource } from "./resources/ListRoomMembersResource.js";
import { ListRoomMessagesResource } from "./resources/ListRoomMessagesResource.js";
import { ListRoomsResource } from "./resources/ListRoomsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  RoomMembershipKey,
  RoomMembership_skip_value_,
  Message_skip_id_,
  Message_skip_value_,
  Room_skip_id_,
  Room_skip_value_,
  User_skip_id_,
  User_skip_value_,
  RoomMembership,
  Message,
  Room,
  User,
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
  readonly memberships: InputDefinition<
    RoomMembershipKey,
    RoomMembership_skip_value_
  >;
  readonly messages: InputDefinition<Message_skip_id_, Message_skip_value_>;
  readonly rooms: InputDefinition<Room_skip_id_, Room_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly checkMembershipResource: ResourceClass<GraphCollections, Json>;
  readonly getMessageResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomMembersResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomMessagesResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomsResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
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
      memberships: new InputDefinition<
        RoomMembershipKey,
        RoomMembership_skip_value_
      >([]),
      messages: new InputDefinition<Message_skip_id_, Message_skip_value_>([]),
      rooms: new InputDefinition<Room_skip_id_, Room_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      checkMembershipResource: CheckMembershipResource,
      getMessageResource: GetMessageResource,
      listRoomMembersResource: ListRoomMembersResource,
      listRoomMessagesResource: ListRoomMessagesResource,
      listRoomsResource: ListRoomsResource,
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
