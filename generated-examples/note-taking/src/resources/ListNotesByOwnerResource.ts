import { NotesByOwnerMapper } from "../mappers/NotesByOwnerMapper.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  User_skip_id_,
  Note,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListNotesByOwnerResourceInputs extends SharedCollections {
  readonly notes: EagerCollection<Note_skip_id_, Note_skip_value_>;
}

export class ListNotesByOwnerResource implements Resource<ListNotesByOwnerResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListNotesByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Note> {
    return inputs.notes.map(NotesByOwnerMapper);
  }
}
