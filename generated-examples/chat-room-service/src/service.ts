import type {
  EagerCollection,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  RoomId,
  RoomValue,
  MessageId,
  MessageValue,
  UserId,
  UserValue,
  RoomMemberId,
  RoomMemberValue,
  RoomsMessagesResourceParams,
  RoomsMembersResourceParams,
} from "./types.js";


export type Inputs = {
  rooms: InputDefinition<RoomId, RoomValue>;
  messages: InputDefinition<MessageId, MessageValue>;
  users: InputDefinition<UserId, UserValue>;
  roomMembers: InputDefinition<RoomMemberId, RoomMemberValue>;
};

export type InputCollections = {
  rooms: EagerCollection<RoomId, RoomValue>;
  messages: EagerCollection<MessageId, MessageValue>;
  users: EagerCollection<UserId, UserValue>;
  roomMembers: EagerCollection<RoomMemberId, RoomMemberValue>;
};

export type GraphCollections = {
  rooms: EagerCollection<RoomId, RoomValue>;
  messages: EagerCollection<MessageId, MessageValue>;
  users: EagerCollection<UserId, UserValue>;
  roomMembers: EagerCollection<RoomMemberId, RoomMemberValue>;
};

export type Resources = {
  readonly "rooms": ResourceClass<GraphCollections, {}>;
  readonly "messages": ResourceClass<GraphCollections, {}>;
  readonly "rooms-messages": ResourceClass<GraphCollections, RoomsMessagesResourceParams>;
  readonly "users": ResourceClass<GraphCollections, {}>;
  readonly "rooms-members": ResourceClass<GraphCollections, RoomsMembersResourceParams>;
};

export class FilterMessagesByRoomMapper implements Mapper<MessageId, MessageValue, MessageId, MessageValue> {
  private roomId: string;

  constructor(roomId: string) {
    this.roomId = roomId;
  }

  mapEntry(
    key: MessageId,
    values: Values<MessageValue>,
    _context: Context
  ): Iterable<[MessageId, MessageValue]> {
    const result: Array<[MessageId, MessageValue]> = Array.of();
    for (const v of values) {
      if (v.roomId === this.roomId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterMembersByRoomMapper implements Mapper<RoomMemberId, RoomMemberValue, RoomMemberId, RoomMemberValue> {
  private roomId: string;

  constructor(roomId: string) {
    this.roomId = roomId;
  }

  mapEntry(
    key: RoomMemberId,
    values: Values<RoomMemberValue>,
    _context: Context
  ): Iterable<[RoomMemberId, RoomMemberValue]> {
    const result: Array<[RoomMemberId, RoomMemberValue]> = Array.of();
    for (const v of values) {
      if (v.roomId === this.roomId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class RoomsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RoomId, RoomValue> {
    return cs.rooms;
  }
}

export class MessagesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<MessageId, MessageValue> {
    return cs.messages;
  }
}

export class RoomsMessagesResource implements Resource<GraphCollections> {
  private roomId: string;

  constructor(params: RoomsMessagesResourceParams) {
    this.roomId = params.roomId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<MessageId, MessageValue> {
    return cs.messages.map(FilterMessagesByRoomMapper, this.roomId);
  }
}

export class UsersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UserId, UserValue> {
    return cs.users;
  }
}

export class RoomsMembersResource implements Resource<GraphCollections> {
  private roomId: string;

  constructor(params: RoomsMembersResourceParams) {
    this.roomId = params.roomId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RoomMemberId, RoomMemberValue> {
    return cs.roomMembers.map(FilterMembersByRoomMapper, this.roomId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
    this.inputs = {
      rooms: new InputDefinition<RoomId, RoomValue>([]),
      messages: new InputDefinition<MessageId, MessageValue>([]),
      users: new InputDefinition<UserId, UserValue>([]),
      roomMembers: new InputDefinition<RoomMemberId, RoomMemberValue>([]),
    };
    this.resources = { "rooms": RoomsResource, "messages": MessagesResource, "rooms-messages": RoomsMessagesResource, "users": UsersResource, "rooms-members": RoomsMembersResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { rooms: inputs.rooms, messages: inputs.messages, users: inputs.users, roomMembers: inputs.roomMembers };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
