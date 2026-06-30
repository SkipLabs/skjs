export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CheckMembershipParams = {
  readonly roomId: string;
  readonly userId: string;
};

export type CreateMessageRequest = { readonly body: string };

export type CreateMessageRequest_skip_id_ = { readonly body: string };

export type CreateMessageRequest_skip_value_ = { readonly body: string };

export type CreateRoomRequest = {
  readonly name: string;
  readonly topic?: string;
};

export type CreateRoomRequest_skip_id_ = {
  readonly name: string;
  readonly topic?: string;
};

export type CreateRoomRequest_skip_value_ = {
  readonly name: string;
  readonly topic?: string;
};

export type GetRoomMessageParams = {
  readonly messageId: string;
  readonly roomId: string;
};

export type GetRoomParams = { readonly roomId: string };

export type GetUserParams = { readonly userId: string };

export type ListRoomMembersParams = { readonly roomId: string };

export type ListRoomMessagesParams = { readonly roomId: string };

export type Message = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly id: string;
  readonly roomId: string;
};

export type MessagePage = {
  readonly messages: Message[];
  readonly total: number;
};

export type MessagePage_skip_id_ = {
  readonly messages: Message[];
  readonly total: number;
};

export type MessagePage_skip_value_ = {
  readonly messages: Message[];
  readonly total: number;
};

export type Message_skip_id_ = string;

export type Message_skip_value_ = {
  readonly authorId: string;
  readonly body: string;
  readonly createdAt: string;
  readonly roomId: string;
};

export type Room = {
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly topic?: string;
  readonly updatedAt?: string;
};

export type RoomMembership = {
  readonly joinedAt: string;
  readonly roomId: string;
  readonly userId: string;
};

export type RoomMembershipKey = {
  readonly roomId: string;
  readonly userId: string;
};

export type RoomMembershipPage = {
  readonly memberships: RoomMembership[];
  readonly total: number;
};

export type RoomMembershipPage_skip_id_ = {
  readonly memberships: RoomMembership[];
  readonly total: number;
};

export type RoomMembershipPage_skip_value_ = {
  readonly memberships: RoomMembership[];
  readonly total: number;
};

export type RoomMembership_skip_id_ = {
  readonly roomId: string;
  readonly userId: string;
};

export type RoomMembership_skip_value_ = { readonly joinedAt: string };

export type RoomPage = { readonly rooms: Room[]; readonly total: number };

export type RoomPage_skip_id_ = {
  readonly rooms: Room[];
  readonly total: number;
};

export type RoomPage_skip_value_ = {
  readonly rooms: Room[];
  readonly total: number;
};

export type Room_skip_id_ = string;

export type Room_skip_value_ = {
  readonly createdAt: string;
  readonly name: string;
  readonly ownerId: string;
  readonly topic?: string;
  readonly updatedAt?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly username?: string;
};

export type UpdateRoomRequest = {
  readonly name?: string;
  readonly topic?: string;
};

export type UpdateRoomRequest_skip_id_ = {
  readonly name?: string;
  readonly topic?: string;
};

export type UpdateRoomRequest_skip_value_ = {
  readonly name?: string;
  readonly topic?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
  readonly username?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly username?: string;
};
