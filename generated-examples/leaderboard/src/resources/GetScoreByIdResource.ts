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
  Json,
} from "@skipruntime/core";

export interface GetScoreByIdResourceInputs extends SharedCollections {
  readonly scores: EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_>;
}

export class GetScoreByIdResource implements Resource<GetScoreByIdResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetScoreByIdResourceInputs,
    _context: Context,
  ): EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_> {
    return inputs.scores;
  }
}
