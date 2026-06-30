import type { Link_skip_id_, Link_skip_value_, Link } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLinkStoredResourceInputs extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
}

export class GetLinkStoredResource implements Resource<GetLinkStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetLinkStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Link_skip_id_, Link_skip_value_> {
    return inputs.links;
  }
}
