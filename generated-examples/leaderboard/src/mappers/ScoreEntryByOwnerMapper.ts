import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntryWithEpochMs,
  User_skip_id_,
  ScoreEntry,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each score entry, emit one output pair whose key is sourced from the entry's ownerUserId field and whose value is the entry's value unchanged. The original score entry id is dropped from the key because the consumer aggregates by owner and does not need the individual entry id.
export class ScoreEntryByOwnerMapper implements Mapper<
  ScoreEntry_skip_id_,
  ScoreEntryWithEpochMs,
  User_skip_id_,
  ScoreEntryWithEpochMs
> {
  mapEntry(
    key: ScoreEntry_skip_id_,
    values: Values<ScoreEntryWithEpochMs>,
    context: Context,
  ): Iterable<[User_skip_id_, ScoreEntryWithEpochMs]> {
    // > body
    const emits: [User_skip_id_, ScoreEntryWithEpochMs][] = [];
    for (const value of values.toArray()) {
      emits.push([value.ownerUserId, value]);
    }
    return emits;
    // < body
  }
}
