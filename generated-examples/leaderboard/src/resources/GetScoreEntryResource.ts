import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ScoreEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetScoreEntryResourceInputs extends SharedCollections {
  readonly scoreEntries: EagerCollection<
    ScoreEntry_skip_id_,
    ScoreEntry_skip_value_
  >;
}

export class GetScoreEntryResource implements Resource<GetScoreEntryResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetScoreEntryResourceInputs,
    _context: Context,
  ): EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_> {
    return inputs.scoreEntries;
  }
}
