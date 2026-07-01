import { FilterBucketsByKeyIdMapper } from "../mappers/FilterBucketsByKeyIdMapper.js";
import type {
  ApiKey_skip_id_,
  Bucket,
  ListBucketsForApiKeyParams,
  ApiKey,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListBucketsForApiKeyResourceInputs extends SharedCollections {
  readonly bucketsByKey: EagerCollection<ApiKey_skip_id_, Bucket>;
}

export class ListBucketsForApiKeyResource implements Resource<ListBucketsForApiKeyResourceInputs> {
  private readonly keyId: string;

  constructor(params: ListBucketsForApiKeyParams) {
    this.keyId = params.keyId;
  }

  instantiate(
    inputs: ListBucketsForApiKeyResourceInputs,
    _context: Context,
  ): EagerCollection<ApiKey_skip_id_, Bucket> {
    return inputs.bucketsByKey.map(FilterBucketsByKeyIdMapper, this.keyId);
  }
}
