import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Component_skip_id_,
  Component_skip_value_,
  Component,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each component entry, when the status param is absent, emit the entry unchanged. Otherwise, emit the entry unchanged when the entry's status field equals the status param; emit nothing otherwise.
export class FilterComponentByStatusMapper implements Mapper<
  Component_skip_id_,
  Component_skip_value_,
  Component_skip_id_,
  Component_skip_value_
> {
  constructor(private status: string | null) {}

  mapEntry(
    key: Component_skip_id_,
    values: Values<Component_skip_value_>,
    context: Context,
  ): Iterable<[Component_skip_id_, Component_skip_value_]> {
    // > body
    const emits: [Component_skip_id_, Component_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.status === null || value.status === this.status) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
