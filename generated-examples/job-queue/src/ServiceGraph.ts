import type {
  Job_skip_id_,
  Job,
  Job_skip_value_,
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
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_jobs = inputs.jobs;
  const output_users = inputs.users;
  return { jobs: output_jobs, users: output_users };
}
