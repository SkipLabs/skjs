import { FilterBoardEntriesMapper } from "../mappers/FilterBoardEntriesMapper.js";
import type {
  Board_skip_id_,
  ScoreEntry,
  ListBoardEntriesParams,
  Board,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListBoardEntriesResourceInputs extends SharedCollections {
  readonly entriesByBoard: EagerCollection<Board_skip_id_, ScoreEntry>;
}

export class ListBoardEntriesResource implements Resource<ListBoardEntriesResourceInputs> {
  private readonly boardId: string;
  private readonly userId: string | null;

  constructor(params: ListBoardEntriesParams) {
    this.boardId = params.boardId;
    this.userId = params.userId ?? null;
  }

  instantiate(
    inputs: ListBoardEntriesResourceInputs,
    _context: Context,
  ): EagerCollection<Board_skip_id_, ScoreEntry> {
    return inputs.entriesByBoard.map(
      FilterBoardEntriesMapper,
      this.boardId,
      this.userId,
    );
  }
}
