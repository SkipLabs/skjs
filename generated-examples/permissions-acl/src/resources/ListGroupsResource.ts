import { FilterGroupByParentMapper } from "../mappers/FilterGroupByParentMapper.js";
import type {
  Group_skip_id_,
  Group_skip_value_,
  ListGroupsParams,
  Group,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListGroupsResourceInputs extends SharedCollections {
  readonly groups: EagerCollection<Group_skip_id_, Group_skip_value_>;
}

export class ListGroupsResource implements Resource<ListGroupsResourceInputs> {
  private readonly parentGroupId: string | null;

  constructor(params: ListGroupsParams) {
    this.parentGroupId = params.parentGroupId ?? null;
  }

  instantiate(
    inputs: ListGroupsResourceInputs,
    _context: Context,
  ): EagerCollection<Group_skip_id_, Group_skip_value_> {
    return inputs.groups.map(FilterGroupByParentMapper, this.parentGroupId);
  }
}
