import type { Group_skip_id_, Group_skip_value_, Group } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GroupsResourceInputs extends SharedCollections {
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
}

export class GroupsResource implements Resource<GroupsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GroupsResourceInputs,
    _context: Context,
  ): EagerCollection<Group_skip_id_, Group_skip_value_> {
    return inputs.groups;
  }
}
