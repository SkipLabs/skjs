import type {
  Link_skip_id_,
  Link,
  Link_skip_value_,
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
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_links = inputs.links;
  const output_users = inputs.users;
  return { links: output_links, users: output_users };
}
