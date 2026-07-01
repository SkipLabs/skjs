import { GetNoteMapper } from "../mappers/GetNoteMapper.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  Note,
  GetNoteParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetNoteResourceInputs extends SharedCollections {
  readonly notes: EagerCollection<Note_skip_id_, Note_skip_value_>;
}

export class GetNoteResource implements Resource<GetNoteResourceInputs> {
  private readonly noteId: string;

  constructor(params: GetNoteParams) {
    this.noteId = params.noteId;
  }

  instantiate(
    inputs: GetNoteResourceInputs,
    _context: Context,
  ): EagerCollection<0, Note> {
    return inputs.notes.map(GetNoteMapper, this.noteId);
  }
}
