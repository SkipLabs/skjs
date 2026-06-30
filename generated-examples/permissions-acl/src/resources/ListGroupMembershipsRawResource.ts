import type {
  GroupMembership_skip_id_,
  GroupMembership_skip_value_,
  GroupMembership,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListGroupMembershipsRawResourceInputs extends SharedCollections {
  readonly groupMemberships: EagerCollection<
    GroupMembership_skip_id_,
    GroupMembership_skip_value_
  >;
}

export class ListGroupMembershipsRawResource implements Resource<ListGroupMembershipsRawResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListGroupMembershipsRawResourceInputs,
    _context: Context,
  ): EagerCollection<GroupMembership_skip_id_, GroupMembership_skip_value_> {
    return inputs.groupMemberships;
  }
}
