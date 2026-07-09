import type {
  AclEntry_skip_id_,
  AclEntry_skip_value_,
  AclEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListAclEntriesInternalResourceInputs extends SharedCollections {
  readonly aclEntries: EagerCollection<AclEntry_skip_id_, AclEntry_skip_value_>;
}

export class ListAclEntriesInternalResource implements Resource<ListAclEntriesInternalResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListAclEntriesInternalResourceInputs,
    _context: Context,
  ): EagerCollection<AclEntry_skip_id_, AclEntry_skip_value_> {
    return inputs.aclEntries;
  }
}
