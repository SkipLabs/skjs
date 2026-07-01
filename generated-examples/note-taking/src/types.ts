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

export type CreateNoteRequest = {
  readonly content: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateNoteRequest_skip_id_ = {
  readonly content: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateNoteRequest_skip_value_ = {
  readonly content: string;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type GetMeParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type GetNoteParams = {
  readonly noteId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListNotesParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type Note = {
  readonly content: string;
  readonly createdAt: string;
  readonly id: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type NoteList = { readonly notes: Note[]; readonly total: number } & {
  readonly [key: string]: Json | null;
};

export type NoteList_skip_id_ = {
  readonly notes: Note[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type NoteList_skip_value_ = {
  readonly notes: Note[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type Note_skip_id_ = string;

export type Note_skip_value_ = {
  readonly content: string;
  readonly createdAt: string;
  readonly ownerId: string;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateNoteRequest = {
  readonly content?: string;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateNoteRequest_skip_id_ = {
  readonly content?: string;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateNoteRequest_skip_value_ = {
  readonly content?: string;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };
