import { FilterNoteByOwnerMapper } from "../mappers/FilterNoteByOwnerMapper.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  ListNotesParams,
  Note,
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
  private readonly userId: string;

  constructor(params: ListNotesParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListNotesByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<Note_skip_id_, Note_skip_value_> {
    return inputs.notes.map(FilterNoteByOwnerMapper, this.userId);
  }
}
