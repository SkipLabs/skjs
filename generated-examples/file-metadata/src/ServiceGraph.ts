import { FileByOwnerHashMapper } from "./mappers/FileByOwnerHashMapper.js";
import { FileByOwnerMapper } from "./mappers/FileByOwnerMapper.js";
import { FileMimeCountKeyMapper } from "./mappers/FileMimeCountKeyMapper.js";
import { IndexStatsByOwnerMapper } from "./mappers/IndexStatsByOwnerMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  IndexedFile_skip_id_,
  IndexedFile,
  IndexedFile_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  OwnerIdKey,
  OwnerHashKey,
  IndexStatsStored,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly files: EagerCollection<
    IndexedFile_skip_id_,
    IndexedFile_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly files: EagerCollection<
    IndexedFile_skip_id_,
    IndexedFile_skip_value_
  >;
  readonly filesByOwner: EagerCollection<OwnerIdKey, IndexedFile>;
  readonly filesByOwnerHash: EagerCollection<OwnerHashKey, IndexedFile>;
  readonly indexStatsByOwner: EagerCollection<User_skip_id_, IndexStatsStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const fileMimeCountKeys = inputs.files.map(FileMimeCountKeyMapper);
  const filesByOwner = inputs.files.map(FileByOwnerMapper);
  const filesByOwnerHash = inputs.files.map(FileByOwnerHashMapper);
  const mimeCountByOwnerMime = fileMimeCountKeys.reduce(SumReducer);
  const indexStatsByOwner = inputs.users.map(
    IndexStatsByOwnerMapper,
    filesByOwner,
    mimeCountByOwnerMime,
  );
  const output_files = inputs.files;
  const output_filesByOwner = filesByOwner;
  const output_filesByOwnerHash = filesByOwnerHash;
  const output_indexStatsByOwner = indexStatsByOwner;
  const output_users = inputs.users;
  return {
    files: output_files,
    filesByOwner: output_filesByOwner,
    filesByOwnerHash: output_filesByOwnerHash,
    indexStatsByOwner: output_indexStatsByOwner,
    users: output_users,
  };
}
