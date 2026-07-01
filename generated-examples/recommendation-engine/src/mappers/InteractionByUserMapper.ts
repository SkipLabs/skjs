import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  User_skip_id_,
  Interaction,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each interaction entry, emit one output pair whose key is sourced from the entry's value's userId field, paired with a new value listing every required field of Interaction explicitly: id sourced from the entry's key (= the original Interaction.id, preserved on the value side so downstream consumers can identify the source Interaction row); userId sourced from the entry's value's userId field; productId sourced from the entry's value's productId field; type sourced from the entry's value's type field; occurredAt sourced from the entry's value's occurredAt field; rating present when the entry's value has a rating field, sourced from the entry's value's rating field, absent otherwise.
export class InteractionByUserMapper implements Mapper<
  Interaction_skip_id_,
  Interaction_skip_value_,
  User_skip_id_,
  Interaction
> {
  mapEntry(
    key: Interaction_skip_id_,
    values: Values<Interaction_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Interaction]> {
    // > body
    const emits: [User_skip_id_, Interaction][] = [];
    for (const value of values.toArray()) {
      const interaction: Interaction = {
        id: key,
        userId: value.userId,
        productId: value.productId,
        type: value.type,
        occurredAt: value.occurredAt,
        ...(value.rating !== undefined && { rating: value.rating }),
      };
      emits.push([value.userId, interaction]);
    }
    return emits;
    // < body
  }
}
