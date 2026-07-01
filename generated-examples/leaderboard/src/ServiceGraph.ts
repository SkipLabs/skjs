import { ScoreEntryByBoardMapper } from "./mappers/ScoreEntryByBoardMapper.js";
import type {
  Board_skip_id_,
  Board,
  Board_skip_value_,
  ScoreEntry_skip_id_,
  ScoreEntry,
  ScoreEntry_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly boards: EagerCollection<Board_skip_id_, Board_skip_value_>;
  readonly scoreEntries: EagerCollection<
    ScoreEntry_skip_id_,
    ScoreEntry_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly boards: EagerCollection<Board_skip_id_, Board_skip_value_>;
  readonly entriesByBoard: EagerCollection<Board_skip_id_, ScoreEntry>;
  readonly scoreEntries: EagerCollection<
    ScoreEntry_skip_id_,
    ScoreEntry_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const entriesByBoard = inputs.scoreEntries.map(ScoreEntryByBoardMapper);
  const output_boards = inputs.boards;
  const output_entriesByBoard = entriesByBoard;
  const output_scoreEntries = inputs.scoreEntries;
  const output_users = inputs.users;
  return {
    boards: output_boards,
    entriesByBoard: output_entriesByBoard,
    scoreEntries: output_scoreEntries,
    users: output_users,
  };
}
