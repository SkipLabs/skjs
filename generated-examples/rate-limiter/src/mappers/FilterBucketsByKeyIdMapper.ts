import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ApiKey_skip_id_, Bucket, ApiKey } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the key: when the entry's key does not equal the keyId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output under the entry's key paired with the value unchanged. (The input collection accumulates all buckets for the same keyId under one key — the upstream BucketByKeyIdMapper re-keys buckets from their composite PK to keyId, so multiple buckets — one per bound policy — typically share the same key; singleton-only access would raise a non-unique-value error on any keyId with two or more buckets.)
export class FilterBucketsByKeyIdMapper implements Mapper<
  ApiKey_skip_id_,
  Bucket,
  ApiKey_skip_id_,
  Bucket
> {
  constructor(private keyId: string) {}

  mapEntry(
    key: ApiKey_skip_id_,
    values: Values<Bucket>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, Bucket]> {
    // > body
    if (key !== this.keyId) return [];
    const emits: [ApiKey_skip_id_, Bucket][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
