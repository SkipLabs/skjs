import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  Interaction,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each interaction entry, emit nothing when the entry's key does not equal the interactionId param. Emit nothing when the entry's value's userId field does not equal the userId param. Otherwise, emit the entry unchanged.
export class GetMyInteractionMapper implements Mapper<
  Interaction_skip_id_,
  Interaction_skip_value_,
  Interaction_skip_id_,
  Interaction_skip_value_
> {
  constructor(
    private userId: string,
    private interactionId: string,
  ) {}

  mapEntry(
    key: Interaction_skip_id_,
    values: Values<Interaction_skip_value_>,
    context: Context,
  ): Iterable<[Interaction_skip_id_, Interaction_skip_value_]> {
    // > body
    if (key !== this.interactionId) return [];
    const emits: [Interaction_skip_id_, Interaction_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.userId === this.userId) emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
