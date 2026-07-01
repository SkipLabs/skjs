import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Sku_skip_id_,
  Sku_skip_value_,
  User_skip_id_,
  Sku,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each sku entry, emit one output pair when the entry's value's ownerId field equals the userId param, otherwise emit nothing. The output key is the userId param (the owner). The output value lists every required field of Sku explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; code sourced from the entry's value's code field; name sourced from the entry's value's name field; createdAt sourced from the entry's value's createdAt field. The optional fields are handled as follows: description is present when the entry's value's description field is present, sourced from the entry's value's description field; absent otherwise. unit is present when the entry's value's unit field is present, sourced from the entry's value's unit field; absent otherwise. reorderThreshold is present when the entry's value's reorderThreshold field is present, sourced from the entry's value's reorderThreshold field; absent otherwise.
export class SkuByOwnerFullMapper implements Mapper<
  Sku_skip_id_,
  Sku_skip_value_,
  User_skip_id_,
  Sku
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Sku_skip_id_,
    values: Values<Sku_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Sku]> {
    // > body
    const emits: [User_skip_id_, Sku][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      const out: Sku = {
        id: key,
        ownerId: value.ownerId,
        code: value.code,
        name: value.name,
        createdAt: value.createdAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
        ...(value.unit !== undefined && { unit: value.unit }),
        ...(value.reorderThreshold !== undefined && {
          reorderThreshold: value.reorderThreshold,
        }),
      };
      emits.push([this.userId, out]);
    }
    return emits;
    // < body
  }
}
