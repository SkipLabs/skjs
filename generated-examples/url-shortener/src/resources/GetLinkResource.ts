import type { Link_skip_id_, Link_skip_value_, Link } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetLinkResourceInputs extends SharedCollections {
  readonly links: EagerCollection<Link_skip_id_, Link_skip_value_>;
}

export class GetLinkResource implements Resource<GetLinkResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetLinkResourceInputs,
    _context: Context,
  ): EagerCollection<Link_skip_id_, Link_skip_value_> {
    return inputs.links;
  }
}
