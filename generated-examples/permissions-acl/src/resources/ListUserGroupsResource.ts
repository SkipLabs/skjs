import type { UserIdKey, GroupMember } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListUserGroupsResourceInputs extends SharedCollections {
  readonly groupMembersByUser: EagerCollection<UserIdKey, GroupMember>;
}

export class ListUserGroupsResource implements Resource<ListUserGroupsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListUserGroupsResourceInputs,
    _context: Context,
  ): EagerCollection<UserIdKey, GroupMember> {
    return inputs.groupMembersByUser;
  }
}
