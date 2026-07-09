import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameLowerKey,
  Tag,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit a new key computed as the entry's value's name field lower-cased, paired with a new value listing every required field of Tag explicitly: id sourced from the entry's key, name sourced from the entry's value's name, ownerId sourced from the entry's value's ownerId, createdAt sourced from the entry's value's createdAt. Optional field updatedAt is present when the entry's value's updatedAt is present, sourced from the entry's value's updatedAt; absent otherwise. The id is re-injected on the value side so that consumers (in particular the updateTag handler) can distinguish a name collision with a DIFFERENT tag from a self-match on the tag being renamed.
export class TagByNameLowerMapper implements Mapper<
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameLowerKey,
  Tag
> {
  mapEntry(
    key: Tag_skip_id_,
    values: Values<Tag_skip_value_>,
    context: Context,
  ): Iterable<[TagNameLowerKey, Tag]> {
    // > body
    const emits: [TagNameLowerKey, Tag][] = [];
    for (const value of values.toArray()) {
      const tag: Tag = {
        id: key,
        name: value.name,
        ownerId: value.ownerId,
        createdAt: value.createdAt,
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.name.toLowerCase(), tag]);
    }
    return emits;
    // < body
  }
}
