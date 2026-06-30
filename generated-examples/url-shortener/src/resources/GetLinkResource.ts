import { FilterLinkByOwnerMapper } from "../mappers/FilterLinkByOwnerMapper.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  GetLinkParams,
  Link,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLinkResourceInputs extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
}

export class GetLinkResource implements Resource<GetLinkResourceInputs> {
  private readonly code: string;
  private readonly userId: string;

  constructor(params: GetLinkParams) {
    this.code = params.code;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetLinkResourceInputs,
    _context: Context,
  ): EagerCollection<Link_skip_id_, Link_skip_value_> {
    return inputs.links.map(FilterLinkByOwnerMapper, this.code, this.userId);
  }
}
