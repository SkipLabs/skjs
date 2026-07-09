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

export type CreateFileRequest = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type CreateFileRequest_skip_id_ = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type CreateFileRequest_skip_value_ = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type IndexStats = {
  readonly mimeTypeBreakdown: MimeTypeCount[];
  readonly totalFiles: number;
  readonly totalSizeBytes: number;
} & { readonly [key: string]: Json | null };

export type IndexStatsStored = {
  readonly mimeTypeBreakdown: MimeTypeCount[];
  readonly totalFiles: number;
  readonly totalSizeBytes: number;
} & { readonly [key: string]: Json | null };

export type IndexStats_skip_id_ = {
  readonly mimeTypeBreakdown: MimeTypeCount[];
  readonly totalFiles: number;
  readonly totalSizeBytes: number;
} & { readonly [key: string]: Json | null };

export type IndexStats_skip_value_ = {
  readonly mimeTypeBreakdown: MimeTypeCount[];
  readonly totalFiles: number;
  readonly totalSizeBytes: number;
} & { readonly [key: string]: Json | null };

export type IndexedFile = {
  readonly createdAt: string;
  readonly description?: string;
  readonly hash?: string;
  readonly id: string;
  readonly mimeType: string;
  readonly ownerId: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags: string[];
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type IndexedFilePage = {
  readonly items: IndexedFile[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type IndexedFilePage_skip_id_ = {
  readonly items: IndexedFile[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type IndexedFilePage_skip_value_ = {
  readonly items: IndexedFile[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
} & { readonly [key: string]: Json | null };

export type IndexedFile_skip_id_ = string;

export type IndexedFile_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType: string;
  readonly ownerId: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags: string[];
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type MimeCountValue = number;

export type MimeTypeCount = {
  readonly count: number;
  readonly mimeType: string;
} & { readonly [key: string]: Json | null };

export type MimeTypeCount_skip_id_ = {
  readonly count: number;
  readonly mimeType: string;
} & { readonly [key: string]: Json | null };

export type MimeTypeCount_skip_value_ = {
  readonly count: number;
  readonly mimeType: string;
} & { readonly [key: string]: Json | null };

export type OwnerFileKey = {
  readonly fileId: string;
  readonly ownerId: string;
} & { readonly [key: string]: Json | null };

export type OwnerHashKey = {
  readonly hash: string;
  readonly ownerId: string;
} & { readonly [key: string]: Json | null };

export type OwnerIdKey = string;

export type OwnerMimeKey = {
  readonly mimeType: string;
  readonly ownerId: string;
} & { readonly [key: string]: Json | null };

export type UpdateFileRequest = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateFileRequest_skip_id_ = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateFileRequest_skip_value_ = {
  readonly description?: string;
  readonly hash?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
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

export type User = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };
