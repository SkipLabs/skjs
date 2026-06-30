import { FilterRoleBindingsMapper } from "../mappers/FilterRoleBindingsMapper.js";
import type {
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  ListRoleBindingsParams,
  RoleBinding,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListRoleBindingsResourceInputs extends SharedCollections {
  readonly roleBindings: EagerCollection<
    RoleBinding_skip_id_,
    RoleBinding_skip_value_
  >;
}

export class ListRoleBindingsResource implements Resource<ListRoleBindingsResourceInputs> {
  private readonly groupId: string | null;
  private readonly resourceId: string | null;
  private readonly roleId: string | null;
  private readonly userId: string | null;

  constructor(params: ListRoleBindingsParams) {
    this.groupId = params.groupId ?? null;
    this.resourceId = params.resourceId ?? null;
    this.roleId = params.roleId ?? null;
    this.userId = params.userId ?? null;
  }

  instantiate(
    inputs: ListRoleBindingsResourceInputs,
    _context: Context,
  ): EagerCollection<RoleBinding_skip_id_, RoleBinding_skip_value_> {
    return inputs.roleBindings.map(
      FilterRoleBindingsMapper,
      this.resourceId,
      this.roleId,
      this.userId,
      this.groupId,
    );
  }
}
