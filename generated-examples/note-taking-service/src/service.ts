import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  NoteId,
  NoteValue,
} from "./types.js";


export type Inputs = {
  notes: InputDefinition<NoteId, NoteValue>;
};

export type InputCollections = {
  notes: EagerCollection<NoteId, NoteValue>;
};

export type GraphCollections = {
  notes: EagerCollection<NoteId, NoteValue>;
};

export type Resources = {
  readonly "notes": ResourceClass<GraphCollections, {}>;
};



export class NotesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NoteId, NoteValue> {
    return cs.notes;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { notes: new InputDefinition<NoteId, NoteValue>([]) };
    this.resources = { "notes": NotesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { notes: inputs.notes };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
