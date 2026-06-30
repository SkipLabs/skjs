import type { Board_skip_id_, Board_skip_value_, Board } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBoardResourceInputs extends SharedCollections {
  readonly boards: EagerCollection<Board_skip_id_, Board_skip_value_>;
}

export class GetBoardResource implements Resource<GetBoardResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetBoardResourceInputs,
    _context: Context,
  ): EagerCollection<Board_skip_id_, Board_skip_value_> {
    return inputs.boards;
  }
}
