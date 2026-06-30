import { FilterBindingsByPolicyIdMapper } from "../mappers/FilterBindingsByPolicyIdMapper.js";
import type {
  Policy_skip_id_,
  Binding,
  ListBindingsByPolicyParams,
  Policy,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListBindingsByPolicyResourceInputs extends SharedCollections {
  readonly bindingsByPolicy: EagerCollection<Policy_skip_id_, Binding>;
}

export class ListBindingsByPolicyResource implements Resource<ListBindingsByPolicyResourceInputs> {
  private readonly policyId: string;

  constructor(params: ListBindingsByPolicyParams) {
    this.policyId = params.policyId;
  }

  instantiate(
    inputs: ListBindingsByPolicyResourceInputs,
    _context: Context,
  ): EagerCollection<Policy_skip_id_, Binding> {
    return inputs.bindingsByPolicy.map(
      FilterBindingsByPolicyIdMapper,
      this.policyId,
    );
  }
}
