import { LinkOwnedByOwnerMapper } from "../mappers/LinkOwnedByOwnerMapper.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  ListMyLinksParams,
  Link,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyLinksResourceInputs extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
}

export class ListMyLinksResource implements Resource<ListMyLinksResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMyLinksParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyLinksResourceInputs,
    _context: Context,
  ): EagerCollection<Link_skip_id_, Link_skip_value_> {
    return inputs.links.map(LinkOwnedByOwnerMapper, this.userId);
  }
}
