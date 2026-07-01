import type { Note_skip_id_, Note_skip_value_, Note } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetNoteResourceInputs extends SharedCollections {
  readonly notes: EagerCollection<Note_skip_id_, Note_skip_value_>;
}

export class GetNoteResource implements Resource<GetNoteResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetNoteResourceInputs,
    _context: Context,
  ): EagerCollection<Note_skip_id_, Note_skip_value_> {
    return inputs.notes;
  }
}
