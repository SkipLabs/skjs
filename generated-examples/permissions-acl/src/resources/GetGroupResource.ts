import type { Group_skip_id_, Group_skip_value_, Group } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetGroupResourceInputs extends SharedCollections {
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
}

export class GetGroupResource implements Resource<GetGroupResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetGroupResourceInputs,
    _context: Context,
  ): EagerCollection<Group_skip_id_, Group_skip_value_> {
    return inputs.groups;
  }
}
