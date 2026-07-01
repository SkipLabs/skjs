import type { Note_skip_id_, Note_skip_value_, Note } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetNoteStoredResourceInputs extends SharedCollections {
  readonly notes: EagerCollection<Note_skip_id_, Note_skip_value_>;
}

export class GetNoteStoredResource implements Resource<GetNoteStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetNoteStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Note_skip_id_, Note_skip_value_> {
    return inputs.notes;
  }
}
