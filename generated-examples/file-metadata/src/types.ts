export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type CreateFileRequest = {
  readonly contentHash: string;
  readonly description?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
};

export type CreateFileRequest_skip_id_ = {
  readonly contentHash: string;
  readonly description?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
};

export type CreateFileRequest_skip_value_ = {
  readonly contentHash: string;
  readonly description?: string;
  readonly mimeType: string;
  readonly path: string;
  readonly sizeBytes: number;
  readonly tags?: string[];
};

export type FileRecord = {
  readonly contentHash: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly mimeType: string;
  readonly ownerId: string;
  readonly path: string;
  readonly revision: number;
  readonly sizeBytes: number;
  readonly tags: string[];
  readonly updatedAt: string;
};

export type FileRecordPage = {
  readonly items: FileRecord[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type FileRecordPage_skip_id_ = {
  readonly items: FileRecord[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type FileRecordPage_skip_value_ = {
  readonly items: FileRecord[];
  readonly limit: number;
  readonly offset: number;
  readonly total: number;
};

export type FileRecord_skip_id_ = string;

export type FileRecord_skip_value_ = {
  readonly contentHash: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly mimeType: string;
  readonly ownerId: string;
  readonly path: string;
  readonly revision: number;
  readonly sizeBytes: number;
  readonly tags: string[];
  readonly updatedAt: string;
};

export type GetFileParams = {
  readonly fileId: string;
  readonly userId: string;
};

export type GetIndexStatsParams = { readonly userId: string };

export type IndexStats = {
  readonly distinctMimeTypeCount: number;
  readonly distinctTagCount: number;
  readonly fileCount: number;
  readonly files: FileRecord[];
  readonly totalSizeBytes: number;
};

export type IndexStatsAccum = {
  readonly fileCount: number;
  readonly mimeTypeCounts: Record<string, number>;
  readonly tagCounts: Record<string, number>;
  readonly totalSizeBytes: number;
};

export type IndexStats_skip_id_ = {
  readonly distinctMimeTypeCount: number;
  readonly distinctTagCount: number;
  readonly fileCount: number;
  readonly files: FileRecord[];
  readonly totalSizeBytes: number;
};

export type IndexStats_skip_value_ = {
  readonly distinctMimeTypeCount: number;
  readonly distinctTagCount: number;
  readonly fileCount: number;
  readonly files: FileRecord[];
  readonly totalSizeBytes: number;
};

export type ListFilesParams = { readonly userId: string };

export type OwnerId = string;

export type StatsSingletonKey = number;

export type UpdateFileRequest = {
  readonly contentHash?: string;
  readonly description?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
};

export type UpdateFileRequest_skip_id_ = {
  readonly contentHash?: string;
  readonly description?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
};

export type UpdateFileRequest_skip_value_ = {
  readonly contentHash?: string;
  readonly description?: string;
  readonly mimeType?: string;
  readonly path?: string;
  readonly sizeBytes?: number;
  readonly tags?: string[];
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
};

export type User = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
};
