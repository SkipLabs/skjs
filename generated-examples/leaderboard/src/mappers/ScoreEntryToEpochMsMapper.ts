import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ScoreEntryWithEpochMs,
  ScoreEntry,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each score entry, emit one output pair whose key is the entry's key unchanged and whose value lists every required field of ScoreEntryWithEpochMs explicitly: id sourced from the value's id field; ownerUserId sourced from the value's ownerUserId field; points sourced from the value's points field; reason sourced from the value's reason field when present, absent otherwise; submittedAtMs sourced from the value's submittedAt field converted to numeric epoch milliseconds (ISO 8601 → epoch ms parsing happens here, at the boundary that converts stored ScoreEntry values into a numeric-timestamp projection consumed by downstream aggregation).
export class ScoreEntryToEpochMsMapper implements Mapper<
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ScoreEntry_skip_id_,
  ScoreEntryWithEpochMs
> {
  mapEntry(
    key: ScoreEntry_skip_id_,
    values: Values<ScoreEntry_skip_value_>,
    context: Context,
  ): Iterable<[ScoreEntry_skip_id_, ScoreEntryWithEpochMs]> {
    // > body
    const emits: [ScoreEntry_skip_id_, ScoreEntryWithEpochMs][] = [];
    for (const value of values.toArray()) {
      const submittedAtMs = new Date(value.submittedAt).getTime();
      const out: ScoreEntryWithEpochMs = {
        id: key,
        ownerUserId: value.ownerUserId,
        points: value.points,
        ...(value.reason !== undefined && { reason: value.reason }),
        submittedAtMs,
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
