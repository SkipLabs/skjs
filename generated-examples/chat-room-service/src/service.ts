import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

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


type Inputs = {
  rooms: Entry<RoomId, RoomValue>[];
  messages: Entry<MessageId, MessageValue>[];
  users: Entry<UserId, UserValue>[];
  roomMembers: Entry<RoomMemberId, RoomMemberValue>[];
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

type Resources = {
  "rooms": new (params: Json) => Resource<GraphCollections>;
  "messages": new (params: Json) => Resource<GraphCollections>;
  "rooms-messages": new (params: Json) => Resource<GraphCollections>;
  "users": new (params: Json) => Resource<GraphCollections>;
  "rooms-members": new (params: Json) => Resource<GraphCollections>;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.roomId === this.roomId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class RoomsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RoomId, RoomValue> {
    return cs.rooms;
  }
}

export class MessagesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as RoomsMessagesResourceParams;
    this.roomId = typed.roomId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<MessageId, MessageValue> {
    return cs.messages.map(FilterMessagesByRoomMapper, this.roomId);
  }
}

export class UsersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as RoomsMembersResourceParams;
    this.roomId = typed.roomId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RoomMemberId, RoomMemberValue> {
    return cs.roomMembers.map(FilterMembersByRoomMapper, this.roomId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyRooms: Entry<RoomId, RoomValue>[] = Array.of();
    const emptyMessages: Entry<MessageId, MessageValue>[] = Array.of();
    const emptyUsers: Entry<UserId, UserValue>[] = Array.of();
    const emptyRoomMembers: Entry<RoomMemberId, RoomMemberValue>[] = Array.of();
    this.initialData = { rooms: emptyRooms, messages: emptyMessages, users: emptyUsers, roomMembers: emptyRoomMembers };
    this.resources = { "rooms": RoomsResource, "messages": MessagesResource, "rooms-messages": RoomsMessagesResource, "users": UsersResource, "rooms-members": RoomsMembersResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { rooms: inputs.rooms, messages: inputs.messages, users: inputs.users, roomMembers: inputs.roomMembers };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
