import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Component_skip_id_,
  ComponentStored,
  Component,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each component entry, emit the entry unchanged when the status param is absent OR when the entry's value's status field equals the status param. Otherwise emit nothing.
export class FilterComponentsByStatusMapper implements Mapper<
  Component_skip_id_,
  ComponentStored,
  Component_skip_id_,
  ComponentStored
> {
  constructor(private status: string | null) {}

  mapEntry(
    key: Component_skip_id_,
    values: Values<ComponentStored>,
    context: Context,
  ): Iterable<[Component_skip_id_, ComponentStored]> {
    // > body
    const emits: [Component_skip_id_, ComponentStored][] = [];
    for (const value of values.toArray()) {
      if (this.status === null || value.status === this.status) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
