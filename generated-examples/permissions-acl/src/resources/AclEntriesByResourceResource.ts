import type { ResourceIdKey, AclEntry } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface AclEntriesByResourceResourceInputs extends SharedCollections {
  readonly aclEntriesByResource: EagerCollection<ResourceIdKey, AclEntry>;
}

export class AclEntriesByResourceResource implements Resource<AclEntriesByResourceResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: AclEntriesByResourceResourceInputs,
    _context: Context,
  ): EagerCollection<ResourceIdKey, AclEntry> {
    return inputs.aclEntriesByResource;
  }
}
