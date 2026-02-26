import type {
  EagerCollection,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  FileId,
  FileValue,
  FileByTypeId,
  FileByTypeValue,
  RecentFileId,
  RecentFileValue,
  FileByTagId,
  FileByTagValue,
} from "./types.js";

export type FileIdAccum = {
  fileIds: string;
  fileCount: number;
};

export type Inputs = {
  files: InputDefinition<FileId, FileValue>;
};

export type InputCollections = {
  files: EagerCollection<FileId, FileValue>;
};

export type GraphCollections = {
  files: EagerCollection<FileId, FileValue>;
  filesByType: EagerCollection<FileByTypeId, FileByTypeValue>;
  recentFiles: EagerCollection<RecentFileId, RecentFileValue>;
  filesByTag: EagerCollection<FileByTagId, FileByTagValue>;
};

export type Resources = {
  "files": ResourceClass<GraphCollections, {}>;
};

export class FileToTypeKeyMapper implements Mapper<FileId, FileValue, string, string> {
  constructor() {
  }

  mapEntry(
    key: FileId,
    values: Values<FileValue>,
    _context: Context
  ): Iterable<[string, string]> {
    const result: Array<[string, string]> = Array.of();
    for (const v of values) {
      result.push([v.extension, key]);
    }
    return result;
  }
}

export class FileIdAccumReducer implements Reducer<string, FileIdAccum> {
  initial: Nullable<FileIdAccum> = null;

  constructor() {
  }

  add(accum: Nullable<FileIdAccum>, value: string & DepSafe): FileIdAccum {
    if (accum === null) {
      return { fileIds: value, fileCount: 1 };
    }
    return {
      fileIds: accum.fileIds + "," + value,
      fileCount: accum.fileCount + 1,
    };
  }

  remove(accum: FileIdAccum, value: string & DepSafe): Nullable<FileIdAccum> {
    const ids = accum.fileIds.split(",");
    const newIds: Array<string> = Array.of();
    for (const id of ids) {
      if (id !== value) {
        newIds.push(id);
      }
    }
    if (newIds.length === 0) {
      return null;
    }
    return { fileIds: newIds.join(","), fileCount: newIds.length };
  }
}

export class FilesByTypeOutputMapper implements Mapper<string, FileIdAccum, FileByTypeId, FileByTypeValue> {
  constructor() {
  }

  mapEntry(
    key: string,
    values: Values<FileIdAccum>,
    _context: Context
  ): Iterable<[FileByTypeId, FileByTypeValue]> {
    const result: Array<[FileByTypeId, FileByTypeValue]> = Array.of();
    for (const accum of values) {
      const value: FileByTypeValue = {
        extension: key,
        fileIds: accum.fileIds,
        fileCount: accum.fileCount,
      };
      result.push([key, value]);
    }
    return result;
  }
}

export class FileToRecentFileMapper implements Mapper<FileId, FileValue, RecentFileId, RecentFileValue> {
  constructor() {
  }

  mapEntry(
    key: FileId,
    values: Values<FileValue>,
    _context: Context
  ): Iterable<[RecentFileId, RecentFileValue]> {
    const result: Array<[RecentFileId, RecentFileValue]> = Array.of();
    for (const v of values) {
      const recentFile: RecentFileValue = {
        name: v.name,
        size: v.size,
        mimeType: v.mimeType,
        extension: v.extension,
        modifiedAt: v.modifiedAt
      };
      result.push([key, recentFile]);
    }
    return result;
  }
}

export class FileToTagKeyMapper implements Mapper<FileId, FileValue, string, string> {
  constructor() {
  }

  mapEntry(
    key: FileId,
    values: Values<FileValue>,
    _context: Context
  ): Iterable<[string, string]> {
    const result: Array<[string, string]> = Array.of();
    for (const v of values) {
      const tags = v.tags.split(",");
      for (const tag of tags) {
        if (tag !== "") {
          result.push([tag, key]);
        }
      }
    }
    return result;
  }
}

export class FilesByTagOutputMapper implements Mapper<string, FileIdAccum, FileByTagId, FileByTagValue> {
  constructor() {
  }

  mapEntry(
    key: string,
    values: Values<FileIdAccum>,
    _context: Context
  ): Iterable<[FileByTagId, FileByTagValue]> {
    const result: Array<[FileByTagId, FileByTagValue]> = Array.of();
    for (const accum of values) {
      const value: FileByTagValue = {
        tag: key,
        fileIds: accum.fileIds,
        fileCount: accum.fileCount,
      };
      result.push([key, value]);
    }
    return result;
  }
}

export class FilesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<FileId, FileValue> {
    return cs.files;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
        this.inputs = { files: new InputDefinition<FileId, FileValue>([]) };
    this.resources = { "files": FilesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const files = inputs.files;

    const filesByTypeGrouped = files.map(FileToTypeKeyMapper).reduce(FileIdAccumReducer);
    const filesByType = filesByTypeGrouped.map(FilesByTypeOutputMapper);

    const recentFiles = files.map(FileToRecentFileMapper);

    const filesByTagGrouped = files.map(FileToTagKeyMapper).reduce(FileIdAccumReducer);
    const filesByTag = filesByTagGrouped.map(FilesByTagOutputMapper);

    return { files, filesByType, recentFiles, filesByTag };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
