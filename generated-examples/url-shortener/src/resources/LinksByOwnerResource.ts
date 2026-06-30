import { FilterLinksByOwnerIdMapper } from "../mappers/FilterLinksByOwnerIdMapper.js";
import type { LinkOwnerId, Link, ListMyLinksParams } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface LinksByOwnerResourceInputs extends SharedCollections {
  readonly linksByOwner: EagerCollection<LinkOwnerId, Link>;
}

export class LinksByOwnerResource implements Resource<LinksByOwnerResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMyLinksParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: LinksByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<LinkOwnerId, Link> {
    return inputs.linksByOwner.map(FilterLinksByOwnerIdMapper, this.userId);
  }
}
