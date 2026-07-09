import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMessageResource } from "./resources/GetMessageResource.js";
import { GetRoomMemberResource } from "./resources/GetRoomMemberResource.js";
import { GetRoomResource } from "./resources/GetRoomResource.js";
import { ListRoomMembersByRoomResource } from "./resources/ListRoomMembersByRoomResource.js";
import { ListRoomMembersByUserResource } from "./resources/ListRoomMembersByUserResource.js";
import { ListRoomMessagesResource } from "./resources/ListRoomMessagesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Message_skip_id_,
  Message_skip_value_,
  RoomMemberCompositeKey,
  RoomMember_skip_value_,
  Room_skip_id_,
  Room_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Message,
  RoomMember,
  Room,
  User,
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
  readonly messages: InputDefinition<Message_skip_id_, Message_skip_value_>;
  readonly roomMembers: InputDefinition<
    RoomMemberCompositeKey,
    RoomMember_skip_value_
  >;
  readonly rooms: InputDefinition<Room_skip_id_, Room_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMessageResource: ResourceClass<GraphCollections, Json>;
  readonly getRoomMemberResource: ResourceClass<GraphCollections, Json>;
  readonly getRoomResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomMembersByRoomResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomMembersByUserResource: ResourceClass<GraphCollections, Json>;
  readonly listRoomMessagesResource: ResourceClass<GraphCollections, Json>;
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
      messages: new InputDefinition<Message_skip_id_, Message_skip_value_>([]),
      roomMembers: new InputDefinition<
        RoomMemberCompositeKey,
        RoomMember_skip_value_
      >([]),
      rooms: new InputDefinition<Room_skip_id_, Room_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getMessageResource: GetMessageResource,
      getRoomMemberResource: GetRoomMemberResource,
      getRoomResource: GetRoomResource,
      listRoomMembersByRoomResource: ListRoomMembersByRoomResource,
      listRoomMembersByUserResource: ListRoomMembersByUserResource,
      listRoomMessagesResource: ListRoomMessagesResource,
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
