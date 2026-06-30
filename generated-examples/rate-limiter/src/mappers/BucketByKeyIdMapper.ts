import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  BucketKey,
  Bucket_skip_value_,
  ApiKey_skip_id_,
  Bucket,
  ApiKey,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each bucket entry, emit one output pair whose key is sourced from the entry's key's keyId component (a foreign key to ApiKey.id, hence typed as ApiKey_skip_id_), paired with a new value listing every required field of Bucket explicitly: keyId sourced from the entry's key's keyId component, policyId sourced from the entry's key's policyId component, ownerId sourced from the entry's value at the ownerId field, kind sourced from the entry's value at the kind field, tokens sourced from the entry's value at the tokens field, lastRefillAt sourced from the entry's value at the lastRefillAt field, count sourced from the entry's value at the count field, and windowStartAt sourced from the entry's value at the windowStartAt field. This re-injects both PK components (keyId and policyId) on the value side so listBucketsForApiKey can construct a BucketState (which requires policyId).
export class BucketByKeyIdMapper implements Mapper<
  BucketKey,
  Bucket_skip_value_,
  ApiKey_skip_id_,
  Bucket
> {
  mapEntry(
    key: BucketKey,
    values: Values<Bucket_skip_value_>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, Bucket]> {
    // > body
    const emits: [ApiKey_skip_id_, Bucket][] = [];
    for (const value of values.toArray()) {
      const bucket: Bucket = {
        keyId: key.keyId,
        policyId: key.policyId,
        ownerId: value.ownerId,
        kind: value.kind,
        ...(value.tokens !== undefined && { tokens: value.tokens }),
        ...(value.lastRefillAt !== undefined && {
          lastRefillAt: value.lastRefillAt,
        }),
        ...(value.count !== undefined && { count: value.count }),
        ...(value.windowStartAt !== undefined && {
          windowStartAt: value.windowStartAt,
        }),
      };
      emits.push([key.keyId, bucket]);
    }
    return emits;
    // < body
  }
}
