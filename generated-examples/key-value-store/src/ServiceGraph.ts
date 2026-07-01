import type {
  KvEntry_skip_id_,
  KvEntry,
  KvEntry_skip_value_,
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
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly entries: EagerCollection<KvEntry_skip_id_, KvEntry_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_entries = inputs.entries;
  const output_users = inputs.users;
  return { entries: output_entries, users: output_users };
}
