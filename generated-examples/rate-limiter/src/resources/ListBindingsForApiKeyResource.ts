import { FilterBindingsByKeyIdMapper } from "../mappers/FilterBindingsByKeyIdMapper.js";
import type {
  ApiKey_skip_id_,
  Binding,
  ListBindingsForApiKeyParams,
  ApiKey,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListBindingsForApiKeyResourceInputs extends SharedCollections {
  readonly bindingsByKey: EagerCollection<ApiKey_skip_id_, Binding>;
}

export class ListBindingsForApiKeyResource implements Resource<ListBindingsForApiKeyResourceInputs> {
  private readonly keyId: string;

  constructor(params: ListBindingsForApiKeyParams) {
    this.keyId = params.keyId;
  }

  instantiate(
    inputs: ListBindingsForApiKeyResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, Binding> {
    return inputs.bindingsByKey.map(FilterBindingsByKeyIdMapper, this.keyId);
  }
}
