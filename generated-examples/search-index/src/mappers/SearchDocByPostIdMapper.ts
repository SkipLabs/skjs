import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  SearchSortKey,
  SearchDocument,
  Post_skip_id_,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit one output pair whose key is sourced from the entry's value's postId field, paired with the entry's value unchanged. The original key's createdAtNeg is dropped because the consumer (single-document lookup by postId) does not need it; the original key's postId is preserved in the value as its postId field.
export class SearchDocByPostIdMapper implements Mapper<
  SearchSortKey,
  SearchDocument,
  Post_skip_id_,
  SearchDocument
> {
  mapEntry(
    key: SearchSortKey,
    values: Values<SearchDocument>,
    context: Context,
  ): Iterable<[Post_skip_id_, SearchDocument]> {
    // > body
    const emits: [Post_skip_id_, SearchDocument][] = [];
    for (const value of values.toArray()) {
      emits.push([value.postId, value]);
    }
    return emits;
    // < body
  }
}
