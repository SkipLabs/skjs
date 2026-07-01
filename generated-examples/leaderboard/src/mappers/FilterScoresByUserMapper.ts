import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ScoreEntry,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each score entry, when the userId param is absent, emit the entry unchanged. When the userId param is present, emit the entry unchanged if and only if the entry's ownerUserId field equals the userId param; otherwise emit nothing.
export class FilterScoresByUserMapper implements Mapper<
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_
> {
  constructor(private userId: string | null) {}

  mapEntry(
    key: ScoreEntry_skip_id_,
    values: Values<ScoreEntry_skip_value_>,
    context: Context,
  ): Iterable<[ScoreEntry_skip_id_, ScoreEntry_skip_value_]> {
    // > body
    const emits: [ScoreEntry_skip_id_, ScoreEntry_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.userId === null || value.ownerUserId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
