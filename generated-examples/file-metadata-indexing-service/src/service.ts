import type {
  EagerCollection,
  Json,
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

export type File = {
  id: string;
  name: string;
  size: number;
  mimeType: string;
  extension: string;
  createdAt: number;
  modifiedAt: number;
  tags: Array<string>;
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

export class FileToTypeKeyMapper implements Mapper<FileId, FileValue, string, File> {
  constructor() {
  }

  mapEntry(
    key: FileId,
    values: Values<FileValue>,
    _context: Context
  ): Iterable<[string, File]> {
    const result: Array<[string, File]> = Array.of();
    for (const v of values) {
      const file: File = {
        id: key,
        name: v.name,
        size: v.size,
        mimeType: v.mimeType,
        extension: v.extension,
        createdAt: v.createdAt,
        modifiedAt: v.modifiedAt,
        tags: v.tags
      };
      result.push([v.extension, file]);
    }
    return result;
  }
}

export class FilesByTypeOutputMapper implements Mapper<string, Array<File>, FileByTypeId, FileByTypeValue> {
  constructor() {
  }

  mapEntry(
    key: string,
    values: Values<Array<File>>,
    _context: Context
  ): Iterable<[FileByTypeId, FileByTypeValue]> {
    const result: Array<[FileByTypeId, FileByTypeValue]> = Array.of();
    for (const filesArray of values) {
      const value: FileByTypeValue = {
        extension: key,
        files: filesArray
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

export class FileToTagKeyMapper implements Mapper<FileId, FileValue, string, File> {
  constructor() {
  }

  mapEntry(
    key: FileId,
    values: Values<FileValue>,
    _context: Context
  ): Iterable<[string, File]> {
    const result: Array<[string, File]> = Array.of();
    for (const v of values) {
      const file: File = {
        id: key,
        name: v.name,
        size: v.size,
        mimeType: v.mimeType,
        extension: v.extension,
        createdAt: v.createdAt,
        modifiedAt: v.modifiedAt,
        tags: v.tags
      };
      const tags = v.tags;
      for (const tag of tags) {
        result.push([tag, file]);
      }
    }
    return result;
  }
}

export class FilesByTagOutputMapper implements Mapper<string, Array<File>, FileByTagId, FileByTagValue> {
  constructor() {
  }

  mapEntry(
    key: string,
    values: Values<Array<File>>,
    _context: Context
  ): Iterable<[FileByTagId, FileByTagValue]> {
    const result: Array<[FileByTagId, FileByTagValue]> = Array.of();
    for (const filesArray of values) {
      const value: FileByTagValue = {
        tag: key,
        files: filesArray
      };
      result.push([key, value]);
    }
    return result;
  }
}

export class FileArrayReducer implements Reducer<File, Array<File>> {
  initial: Nullable<Array<File>> = null;

  constructor() {
  }

  add(accum: Nullable<Array<File>>, value: File & DepSafe): Array<File> {
    if (accum === null) {
      return Array.of(value);
    }
    const newArray: Array<File> = Array.of();
    for (const item of accum) {
      newArray.push(item);
    }
    newArray.push(value);
    return newArray;
  }

  remove(accum: Array<File>, value: File & DepSafe): Nullable<Array<File>> {
    const newArray: Array<File> = Array.of();
    for (const item of accum) {
      if (item.id !== value.id) {
        newArray.push(item);
      }
    }
    if (newArray.length === 0) {
      return null;
    }
    return newArray;
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
    
    const filesByTypeGrouped = files.map(FileToTypeKeyMapper).reduce(FileArrayReducer);
    const filesByType = filesByTypeGrouped.map(FilesByTypeOutputMapper);
    
    const recentFiles = files.map(FileToRecentFileMapper);
    
    const filesByTagGrouped = files.map(FileToTagKeyMapper).reduce(FileArrayReducer);
    const filesByTag = filesByTagGrouped.map(FilesByTagOutputMapper);
    
    return { files, filesByType, recentFiles, filesByTag };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
