import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code?: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type EntriesByUserMapperOut = {
  readonly createdAt: string;
  readonly key: string;
  readonly revision: number;
  readonly updatedAt: string;
  readonly userId: string;
  readonly value: Record<string, Json>;
} & { readonly [key: string]: Json | null };

export type EntryList = {
  readonly entries: KvEntry[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type EntryList_skip_id_ = {
  readonly entries: KvEntry[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type EntryList_skip_value_ = {
  readonly entries: KvEntry[];
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type GetEntryParams = {
  readonly key: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type KvEntry = {
  readonly createdAt: string;
  readonly key: string;
  readonly revision: number;
  readonly updatedAt: string;
  readonly userId: string;
  readonly value: Json;
} & { readonly [key: string]: Json | null };

export type KvEntry_skip_id_ = {
  readonly key: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type KvEntry_skip_value_ = {
  readonly createdAt: string;
  readonly revision: number;
  readonly updatedAt: string;
  readonly value: Json;
} & { readonly [key: string]: Json | null };

export type ListEntriesParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type PutEntryRequest = { readonly value: Json } & {
  readonly [key: string]: Json | null;
};

export type PutEntryRequest_skip_id_ = { readonly value: Json } & {
  readonly [key: string]: Json | null;
};

export type PutEntryRequest_skip_value_ = { readonly value: Json } & {
  readonly [key: string]: Json | null;
};

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

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type UserId = string;

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
