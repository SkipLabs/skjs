import { FilterApiKeysByOwnerMapper } from "../mappers/FilterApiKeysByOwnerMapper.js";
import type {
  ApiKey_skip_id_,
  ApiKey_skip_value_,
  ListApiKeysParams,
  ApiKey,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListApiKeysResourceInputs extends SharedCollections {
  readonly apiKeys: EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_>;
}

export class ListApiKeysResource implements Resource<ListApiKeysResourceInputs> {
  private readonly userId: string;

  constructor(params: ListApiKeysParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListApiKeysResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_> {
    return inputs.apiKeys.map(FilterApiKeysByOwnerMapper, this.userId);
  }
}
