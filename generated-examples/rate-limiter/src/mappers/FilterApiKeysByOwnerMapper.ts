import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ApiKey_skip_id_, ApiKey_skip_value_, ApiKey } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each api key entry, emit the entry unchanged when the entry's ownerId field equals the userId param. Otherwise emit nothing.
export class FilterApiKeysByOwnerMapper implements Mapper<
  ApiKey_skip_id_,
  ApiKey_skip_value_,
  ApiKey_skip_id_,
  ApiKey_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: ApiKey_skip_id_,
    values: Values<ApiKey_skip_value_>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, ApiKey_skip_value_]> {
    // > body
    const emits: [ApiKey_skip_id_, ApiKey_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
