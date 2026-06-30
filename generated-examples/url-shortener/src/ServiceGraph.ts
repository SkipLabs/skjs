import { LinksByOwnerMapper } from "./mappers/LinksByOwnerMapper.js";
import type {
  Link_skip_id_,
  Link,
  Link_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  LinkOwnerId,
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
  readonly linksByOwner: EagerCollection<LinkOwnerId, Link>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const linksByOwner = inputs.links.map(LinksByOwnerMapper);
  const output_links = inputs.links;
  const output_linksByOwner = linksByOwner;
  const output_users = inputs.users;
  return {
    links: output_links,
    linksByOwner: output_linksByOwner,
    users: output_users,
  };
}
