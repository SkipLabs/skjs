import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type EntryListResponse = {
  readonly entries: KvEntry[];
  readonly total: number;
};

export type EntryListResponse_skip_id_ = {
  readonly entries: KvEntry[];
  readonly total: number;
};

export type EntryListResponse_skip_value_ = {
  readonly entries: KvEntry[];
  readonly total: number;
};

export type KvEntry = {
  readonly createdAt: string;
  readonly key: string;
  readonly updatedAt: string;
  readonly value: Json;
};

export type KvEntry_skip_id_ = string;

export type KvEntry_skip_value_ = {
  readonly createdAt: string;
  readonly updatedAt: string;
  readonly value: Json;
};

export type ListEntriesParams = { readonly prefix?: string };

export type PutEntryRequest = { readonly value: Json };

export type PutEntryRequest_skip_id_ = { readonly value: Json };

export type PutEntryRequest_skip_value_ = { readonly value: Json };
