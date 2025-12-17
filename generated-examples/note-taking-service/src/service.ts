import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context
} from "@skipruntime/core";

import type {
  NoteId,
  NoteValue,
} from "./types.js";


type Inputs = {
  notes: Entry<NoteId, NoteValue>[];
};

export type InputCollections = {
  notes: EagerCollection<NoteId, NoteValue>;
};

export type GraphCollections = {
  notes: EagerCollection<NoteId, NoteValue>;
};

type Resources = {
  "notes": new (params: Json) => Resource<GraphCollections>;
};



export class NotesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NoteId, NoteValue> {
    return cs.notes;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyNotes: Entry<NoteId, NoteValue>[] = Array.of();
    this.initialData = { notes: emptyNotes };
    this.resources = { "notes": NotesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { notes: inputs.notes };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
