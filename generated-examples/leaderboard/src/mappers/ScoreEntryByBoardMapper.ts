import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  Board_skip_id_,
  ScoreEntry,
  Board,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each score entry, emit one output pair whose key is sourced from the entry's value's boardId field, and whose value lists every required field of ScoreEntry explicitly: id sourced from the entry's key; boardId, userId, points, createdAt sourced from the entry's value; note is optional, present when the entry's value has a note field (sourced from there), absent otherwise. The original entry id, no longer part of the new key, is preserved in the value as id so downstream consumers can reconstruct the full ScoreEntry.
export class ScoreEntryByBoardMapper implements Mapper<
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  Board_skip_id_,
  ScoreEntry
> {
  mapEntry(
    key: ScoreEntry_skip_id_,
    values: Values<ScoreEntry_skip_value_>,
    context: Context,
  ): Iterable<[Board_skip_id_, ScoreEntry]> {
    // > body
    const emits: [Board_skip_id_, ScoreEntry][] = [];
    for (const value of values.toArray()) {
      const entry: ScoreEntry = {
        id: key,
        boardId: value.boardId,
        userId: value.userId,
        points: value.points,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([value.boardId, entry]);
    }
    return emits;
    // < body
  }
}
