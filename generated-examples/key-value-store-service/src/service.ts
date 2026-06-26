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
  KVEntryId,
  KVEntryValue,
} from "./types.js";


export type Inputs = {
  entries: InputDefinition<KVEntryId, KVEntryValue>;
};

export type InputCollections = {
  entries: EagerCollection<KVEntryId, KVEntryValue>;
};

export type GraphCollections = {
  entries: EagerCollection<KVEntryId, KVEntryValue>;
};

export type Resources = {
  readonly "entries": ResourceClass<GraphCollections, {}>;
};

export class EntriesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<KVEntryId, KVEntryValue> {
    return cs.entries;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { entries: new InputDefinition<KVEntryId, KVEntryValue>([]) };
    this.resources = { "entries": EntriesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { entries: inputs.entries };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
