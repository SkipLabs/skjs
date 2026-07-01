import { FilterScoresByUserMapper } from "../mappers/FilterScoresByUserMapper.js";
import type {
  ScoreEntry_skip_id_,
  ScoreEntry_skip_value_,
  ListScoresParams,
  ScoreEntry,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListScoresResourceInputs extends SharedCollections {
  readonly scores: EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_>;
}

export class ListScoresResource implements Resource<ListScoresResourceInputs> {
  private readonly userId: string | null;

  constructor(params: ListScoresParams) {
    this.userId = params.userId ?? null;
  }

  instantiate(
    inputs: ListScoresResourceInputs,
    _context: Context,
  ): EagerCollection<ScoreEntry_skip_id_, ScoreEntry_skip_value_> {
    return inputs.scores.map(FilterScoresByUserMapper, this.userId);
  }
}
