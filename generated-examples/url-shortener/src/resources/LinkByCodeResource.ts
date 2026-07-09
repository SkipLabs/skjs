import { LinkByCodeMapper } from "../mappers/LinkByCodeMapper.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  LinkShortCode,
  Link,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface LinkByCodeResourceInputs extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
}

export class LinkByCodeResource implements Resource<LinkByCodeResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: LinkByCodeResourceInputs,
    _context: Context,
  ): EagerCollection<LinkShortCode, Link> {
    return inputs.links.map(LinkByCodeMapper);
  }
}
