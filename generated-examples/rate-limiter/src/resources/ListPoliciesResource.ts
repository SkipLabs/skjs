import { PolicyByOwnerMapper } from "../mappers/PolicyByOwnerMapper.js";
import type {
  Policy_skip_id_,
  Policy_skip_value_,
  ListPoliciesParams,
  Policy,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPoliciesResourceInputs extends SharedCollections {
  readonly policies: EagerCollection<Policy_skip_id_, Policy_skip_value_>;
}

export class ListPoliciesResource implements Resource<ListPoliciesResourceInputs> {
  private readonly userId: string;

  constructor(params: ListPoliciesParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListPoliciesResourceInputs,
    _context: Context,
  ): EagerCollection<Policy_skip_id_, Policy_skip_value_> {
    return inputs.policies.map(PolicyByOwnerMapper, this.userId);
  }
}
