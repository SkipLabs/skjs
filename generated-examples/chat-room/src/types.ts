import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CreateMessageRequest = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreateMessageRequest_skip_id_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreateMessageRequest_skip_value_ = { readonly content: string } & {
  readonly [key: string]: Json | null;
};

export type CreateRoomRequest = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type CreateRoomRequest_skip_id_ = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type CreateRoomRequest_skip_value_ = {
  readonly name: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type GetRoomMessageParams = { readonly messageId: string } & {
  readonly [key: string]: Json | null;
};

export type GetRoomParams = { readonly roomId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserParams = { readonly targetUserId: string } & {
  readonly [key: string]: Json | null;
};

export type ListRoomMembersParams = { readonly roomId: string } & {
  readonly [key: string]: Json | null;
};

export type ListRoomMessagesParams = { readonly roomId: string } & {
  readonly [key: string]: Json | null;
};

export type Message = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly roomId: string;
} & { readonly [key: string]: Json | null };

export type MessageList = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type MessageList_skip_id_ = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type MessageList_skip_value_ = { readonly messages: Message[] } & {
  readonly [key: string]: Json | null;
};

export type MessageOrderKey = {
  readonly createdAt: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type Message_skip_id_ = string;

export type Message_skip_value_ = {
  readonly authorId: string;
  readonly content: string;
  readonly createdAt: string;
  readonly roomId: string;
} & { readonly [key: string]: Json | null };

export type Room = {
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type RoomList = { readonly rooms: Room[] } & {
  readonly [key: string]: Json | null;
};

export type RoomList_skip_id_ = { readonly rooms: Room[] } & {
  readonly [key: string]: Json | null;
};

export type RoomList_skip_value_ = { readonly rooms: Room[] } & {
  readonly [key: string]: Json | null;
};

export type RoomMember = {
  readonly joinedAt: string;
  readonly roomId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type RoomMemberCompositeKey = {
  readonly roomId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type RoomMemberList = { readonly members: RoomMember[] } & {
  readonly [key: string]: Json | null;
};

export type RoomMemberList_skip_id_ = { readonly members: RoomMember[] } & {
  readonly [key: string]: Json | null;
};

export type RoomMemberList_skip_value_ = { readonly members: RoomMember[] } & {
  readonly [key: string]: Json | null;
};

export type RoomMember_skip_id_ = {
  readonly roomId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type RoomMember_skip_value_ = { readonly joinedAt: string } & {
  readonly [key: string]: Json | null;
};

export type Room_skip_id_ = string;

export type Room_skip_value_ = {
  readonly createdAt: string;
  readonly name: string;
  readonly ownerId: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };

export type UpdateRoomRequest = {
  readonly name?: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type UpdateRoomRequest_skip_id_ = {
  readonly name?: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type UpdateRoomRequest_skip_value_ = {
  readonly name?: string;
  readonly topic?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
} & { readonly [key: string]: Json | null };
