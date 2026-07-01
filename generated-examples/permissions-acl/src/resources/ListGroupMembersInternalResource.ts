import type {
  GroupMember_skip_id_,
  GroupMember_skip_value_,
  GroupMember,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListGroupMembersInternalResourceInputs extends SharedCollections {
  readonly groupMembers: EagerCollection<
    GroupMember_skip_id_,
    GroupMember_skip_value_
  >;
}

export class ListGroupMembersInternalResource implements Resource<ListGroupMembersInternalResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListGroupMembersInternalResourceInputs,
    _context: Context,
  ): EagerCollection<GroupMember_skip_id_, GroupMember_skip_value_> {
    return inputs.groupMembers;
  }
}
