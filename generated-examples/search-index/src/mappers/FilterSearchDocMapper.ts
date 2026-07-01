import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { SearchSortKey, SearchDocument } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, apply the three optional filters in sequence. (1) When the authorId param is present AND the entry's value's authorId field does not equal the authorId param, emit nothing. (2) When the tagName param is present AND no element of the entry's value's tagNames array (lowercased) equals the tagName param (lowercased), emit nothing. (3) When the q param is present AND its value (lowercased) is NOT a substring of the concatenation of the entry's value's title field, the literal space, body field, the literal space, authorUsername field (defaulted to the empty string when absent), the literal space, authorDisplayName field (defaulted to the empty string when absent), the literal space, and the entry's value's tagNames array joined by the literal space — all lowercased — emit nothing. Otherwise emit the entry unchanged.
export class FilterSearchDocMapper implements Mapper<
  SearchSortKey,
  SearchDocument,
  SearchSortKey,
  SearchDocument
> {
  constructor(
    private q: string | null,
    private tagName: string | null,
    private authorId: string | null,
  ) {}

  mapEntry(
    key: SearchSortKey,
    values: Values<SearchDocument>,
    context: Context,
  ): Iterable<[SearchSortKey, SearchDocument]> {
    // > body
    const emits: [SearchSortKey, SearchDocument][] = [];
    const qLower = this.q !== null ? this.q.toLowerCase() : null;
    const tagLower = this.tagName !== null ? this.tagName.toLowerCase() : null;
    for (const value of values.toArray()) {
      if (this.authorId !== null && value.authorId !== this.authorId) continue;
      if (tagLower !== null) {
        let found = false;
        for (const t of value.tagNames) {
          if (t.toLowerCase() === tagLower) {
            found = true;
            break;
          }
        }
        if (!found) continue;
      }
      if (qLower !== null) {
        const username =
          value.authorUsername !== undefined ? value.authorUsername : "";
        const display =
          value.authorDisplayName !== undefined ? value.authorDisplayName : "";
        const joined = (
          value.title +
          " " +
          value.body +
          " " +
          username +
          " " +
          display +
          " " +
          value.tagNames.join(" ")
        ).toLowerCase();
        if (!joined.includes(qLower)) continue;
      }
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
