import type { BucketKey, Bucket_skip_value_, Bucket } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBucketResourceInputs extends SharedCollections {
  readonly buckets: EagerCollection<BucketKey, Bucket_skip_value_>;
}

export class GetBucketResource implements Resource<GetBucketResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetBucketResourceInputs,
    _context: Context,
  ): EagerCollection<BucketKey, Bucket_skip_value_> {
    return inputs.buckets;
  }
}
