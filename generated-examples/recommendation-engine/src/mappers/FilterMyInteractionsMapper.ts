import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  Interaction,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each interaction entry, emit the entry unchanged when the entry's userId field equals the userId param AND (the type param is absent OR the entry's type field equals the type param) AND (the productId param is absent OR the entry's productId field equals the productId param). Otherwise emit nothing.
export class FilterMyInteractionsMapper implements Mapper<
  Interaction_skip_id_,
  Interaction_skip_value_,
  Interaction_skip_id_,
  Interaction_skip_value_
> {
  constructor(
    private userId: string,
    private type: string | null,
    private productId: string | null,
  ) {}

  mapEntry(
    key: Interaction_skip_id_,
    values: Values<Interaction_skip_value_>,
    context: Context,
  ): Iterable<[Interaction_skip_id_, Interaction_skip_value_]> {
    // > body
    const emits: [Interaction_skip_id_, Interaction_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.userId !== this.userId) continue;
      if (this.type !== null && value.type !== this.type) continue;
      if (this.productId !== null && value.productId !== this.productId)
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
