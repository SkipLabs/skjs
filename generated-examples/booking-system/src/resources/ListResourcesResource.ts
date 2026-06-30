import { FilterResourcesByOwnerMapper } from "../mappers/FilterResourcesByOwnerMapper.js";
import type {
  BookableResource_skip_id_,
  BookableResource_skip_value_,
  ListResourcesParams,
  BookableResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListResourcesResourceInputs extends SharedCollections {
  readonly resources: EagerCollection<
    BookableResource_skip_id_,
    BookableResource_skip_value_
  >;
}

export class ListResourcesResource implements Resource<ListResourcesResourceInputs> {
  private readonly ownerId: string | null;

  constructor(params: ListResourcesParams) {
    this.ownerId = params.ownerId ?? null;
  }

  instantiate(
    inputs: ListResourcesResourceInputs,
    _context: Context,
  ): EagerCollection<BookableResource_skip_id_, BookableResource_skip_value_> {
    return inputs.resources.map(FilterResourcesByOwnerMapper, this.ownerId);
  }
}
