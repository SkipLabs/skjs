import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Board_skip_id_, ScoreEntry, Board } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the boardId key, when the entry's key does not equal the boardId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, when the userId param is absent OR the value's userId field equals the userId param, emit one output under the entry's key paired with the value (the value is emitted unchanged; its boardId field already equals the entry's key). When the userId param is absent, every value in the values list is emitted; when present, only those values whose userId field matches are emitted. The input collection accumulates all score entries for the same board under one key — singleton-only access would raise on any board with two or more entries, which is the common case.
export class FilterBoardEntriesMapper implements Mapper<
  Board_skip_id_,
  ScoreEntry,
  Board_skip_id_,
  ScoreEntry
> {
  constructor(
    private boardId: string,
    private userId: string | null,
  ) {}

  mapEntry(
    key: Board_skip_id_,
    values: Values<ScoreEntry>,
    context: Context,
  ): Iterable<[Board_skip_id_, ScoreEntry]> {
    // > body
    if (key !== this.boardId) return [];
    const emits: [Board_skip_id_, ScoreEntry][] = [];
    for (const value of values.toArray()) {
      if (this.userId === null || value.userId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
