import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  Interaction,
  Interaction_skip_id_,
  Interaction_skip_value_,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under a userId key: when the entry's key does not equal the userId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list: when the productId param is present and the value's productId field does not equal the productId param, emit nothing for this value; when the type param is present and the value's type field does not equal the type param, emit nothing for this value; otherwise emit one output pair whose key is sourced from the value's id field and whose value lists every field of Interaction_skip_value_ sourced from the value (userId, productId, type, occurredAt, and rating when present). The upstream interactionsByUser collection accumulates all interactions for the same user under one key, so iteration over the values list is required — singleton-only access would raise on any user with two or more interactions.
export class ListMyInteractionsMapper implements Mapper<
  User_skip_id_,
  Interaction,
  Interaction_skip_id_,
  Interaction_skip_value_
> {
  constructor(
    private userId: string,
    private productId: string | null,
    private type: string | null,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<Interaction>,
    context: Context,
  ): Iterable<[Interaction_skip_id_, Interaction_skip_value_]> {
    // > body
    if (key !== this.userId) return [];
    const emits: [Interaction_skip_id_, Interaction_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.productId !== null && value.productId !== this.productId)
        continue;
      if (this.type !== null && value.type !== this.type) continue;
      const out: Interaction_skip_value_ = {
        userId: value.userId,
        productId: value.productId,
        type: value.type,
        occurredAt: value.occurredAt,
        ...(value.rating !== undefined && { rating: value.rating }),
      };
      emits.push([value.id, out]);
    }
    return emits;
    // < body
  }
}
