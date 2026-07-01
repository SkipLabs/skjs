import type {
  AclResource_skip_id_,
  AclResource_skip_value_,
  AclResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ResourcesResourceInputs extends SharedCollections {
  readonly resources: EagerCollection<
    AclResource_skip_id_,
    AclResource_skip_value_
  >;
}

export class ResourcesResource implements Resource<ResourcesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ResourcesResourceInputs,
    _context: Context,
  ): EagerCollection<AclResource_skip_id_, AclResource_skip_value_> {
    return inputs.resources;
  }
}
