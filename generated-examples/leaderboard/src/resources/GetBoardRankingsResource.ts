import { RankingComputeMapper } from "../mappers/RankingComputeMapper.js";
import type {
  Board_skip_id_,
  Board_skip_value_,
  ScoreEntry,
  Ranking,
  GetBoardRankingsParams,
  Board,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBoardRankingsResourceInputs extends SharedCollections {
  readonly boards: EagerCollection<Board_skip_id_, Board_skip_value_>;
  readonly entriesByBoard: EagerCollection<Board_skip_id_, ScoreEntry>;
}

export class GetBoardRankingsResource implements Resource<GetBoardRankingsResourceInputs> {
  private readonly boardId: string;

  constructor(params: GetBoardRankingsParams) {
    this.boardId = params.boardId;
  }

  instantiate(
    inputs: GetBoardRankingsResourceInputs,
    _context: Context,
  ): EagerCollection<0, Ranking> {
    return inputs.boards.map(
      RankingComputeMapper,
      this.boardId,
      inputs.entriesByBoard,
    );
  }
}
