import type { GroupIdKey, GroupMember } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListGroupMembersResourceInputs extends SharedCollections {
  readonly groupMembersByGroup: EagerCollection<GroupIdKey, GroupMember>;
}

export class ListGroupMembersResource implements Resource<ListGroupMembersResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListGroupMembersResourceInputs,
    _context: Context,
  ): EagerCollection<GroupIdKey, GroupMember> {
    return inputs.groupMembersByGroup;
  }
}
