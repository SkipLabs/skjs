import type {
  FileRecord_skip_id_,
  FileRecord,
  FileRecord_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_files = inputs.files;
  const output_users = inputs.users;
  return { files: output_files, users: output_users };
}
