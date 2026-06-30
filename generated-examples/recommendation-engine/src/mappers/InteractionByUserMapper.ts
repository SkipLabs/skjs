import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  User_skip_id_,
  Interaction,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each interaction entry, emit one output pair whose key is sourced from the entry's value at the userId field (the User primary key), paired with a new value of type Interaction listing every required field explicitly: id sourced from the entry's key (the original Interaction primary key), userId sourced from the entry's value at userId, productId sourced from the entry's value at productId, type sourced from the entry's value at type, occurredAt sourced from the entry's value at occurredAt, and rating sourced from the entry's value at rating when present. This preserves the original interaction id which would otherwise be lost in the re-key, since Interaction_skip_value_ excludes the id field by construction.
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
