import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Workspace_skip_id_,
  Workspace_skip_value_,
  User_skip_id_,
  Membership,
  Workspace,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each workspace entry, consult membershipsByUser for the membership values indexed by the userId param. Build the set of workspaceIds from those membership values (each membership value carries a required workspaceId field). Emit the entry unchanged when the entry's key is in that set. Otherwise emit nothing.
export class WorkspacesForUserMapper implements Mapper<
  Workspace_skip_id_,
  Workspace_skip_value_,
  Workspace_skip_id_,
  Workspace_skip_value_
> {
  constructor(
    private userId: string,
    private membershipsByUser: EagerCollection<User_skip_id_, Membership>,
  ) {}

  mapEntry(
    key: Workspace_skip_id_,
    values: Values<Workspace_skip_value_>,
    context: Context,
  ): Iterable<[Workspace_skip_id_, Workspace_skip_value_]> {
    // > body
    const memberships = this.membershipsByUser.getArray(this.userId);
    const workspaceIds = new Set<string>();
    for (const membership of memberships) {
      workspaceIds.add(membership.workspaceId);
    }
    if (!workspaceIds.has(key)) return [];
    const emits: [Workspace_skip_id_, Workspace_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
