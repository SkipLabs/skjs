export type FileId = string;

export type FileValue = {
  name: string;
  size: number;
  mimeType: string;
  extension: string;
  createdAt: number;
  modifiedAt: number;
  tags: string;
};

export type File = FileValue & { id: FileId };

export type FileByTypeId = string;

export type FileByTypeValue = {
  extension: string;
  fileIds: string;
  fileCount: number;
};

export type FileByType = FileByTypeValue & { id: FileByTypeId };

export type RecentFileId = string;

export type RecentFileValue = {
  name: string;
  size: number;
  mimeType: string;
  extension: string;
  modifiedAt: number;
};

export type RecentFile = RecentFileValue & { id: RecentFileId };

export type FileByTagId = string;

export type FileByTagValue = {
  tag: string;
  fileIds: string;
  fileCount: number;
};

export type FileByTag = FileByTagValue & { id: FileByTagId };
