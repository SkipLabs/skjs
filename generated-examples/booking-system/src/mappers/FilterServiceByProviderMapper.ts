import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Service_skip_id_,
  Service_skip_value_,
  Service,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each service entry, when the providerId param is absent, emit the entry unchanged. Otherwise, emit the entry unchanged when the entry's value providerId field equals the providerId param; emit nothing otherwise.
export class FilterServiceByProviderMapper implements Mapper<
  Service_skip_id_,
  Service_skip_value_,
  Service_skip_id_,
  Service_skip_value_
> {
  constructor(private providerId: string | null) {}

  mapEntry(
    key: Service_skip_id_,
    values: Values<Service_skip_value_>,
    context: Context,
  ): Iterable<[Service_skip_id_, Service_skip_value_]> {
    // > body
    const emits: [Service_skip_id_, Service_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.providerId === null || value.providerId === this.providerId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
