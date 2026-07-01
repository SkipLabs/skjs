import type { ApiKey_skip_id_, ApiKey_skip_value_, ApiKey } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetApiKeyResourceInputs extends SharedCollections {
  readonly apiKeys: EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_>;
}

export class GetApiKeyResource implements Resource<GetApiKeyResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetApiKeyResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, ApiKey_skip_value_> {
    return inputs.apiKeys;
  }
}
