export type RoomId = string;

export type RoomValue = {
  name: string;
  createdAt: number;
  createdBy: string;
};

export type Room = RoomValue & { id: RoomId };

export type MessageId = string;

export type MessageValue = {
  roomId: string;
  authorId: string;
  content: string;
  timestamp: number;
};

export type Message = MessageValue & { id: MessageId };

export type UserId = string;

export type UserValue = {
  username: string;
  displayName: string;
  lastSeen: number | null;
};

export type User = UserValue & { id: UserId };

export type RoomMemberId = string;

export type RoomMemberValue = {
  roomId: string;
  userId: string;
  joinedAt: number;
};

export type RoomMember = RoomMemberValue & { id: RoomMemberId };

export type RoomsMessagesResourceParams = {
  roomId: string;
};

export type RoomsMembersResourceParams = {
  roomId: string;
};
