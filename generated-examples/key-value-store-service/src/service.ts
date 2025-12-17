import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context
} from "@skipruntime/core";

import type {
  KVEntryId,
  KVEntryValue,
} from "./types.js";


type Inputs = {
  entries: Entry<KVEntryId, KVEntryValue>[];
};

export type InputCollections = {
  entries: EagerCollection<KVEntryId, KVEntryValue>;
};

export type GraphCollections = {
  entries: EagerCollection<KVEntryId, KVEntryValue>;
};

type Resources = {
  "entries": new (params: Json) => Resource<GraphCollections>;
};

export class EntriesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<KVEntryId, KVEntryValue> {
    return cs.entries;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyKVEntrys: Entry<KVEntryId, KVEntryValue>[] = Array.of();
    this.initialData = { entries: emptyKVEntrys };
    this.resources = { "entries": EntriesResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { entries: inputs.entries };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
