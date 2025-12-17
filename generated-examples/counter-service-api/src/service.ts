import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context
} from "@skipruntime/core";

import type {
  CounterId,
  CounterValue,
} from "./types.js";


type Inputs = {
  counters: Entry<CounterId, CounterValue>[];
};

export type InputCollections = {
  counters: EagerCollection<CounterId, CounterValue>;
};

export type GraphCollections = {
  counters: EagerCollection<CounterId, CounterValue>;
};

type Resources = {
  "counters": new (params: Json) => Resource<GraphCollections>;
};



export class CountersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CounterId, CounterValue> {
    return cs.counters;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyCounters: Entry<CounterId, CounterValue>[] = Array.of();
    this.initialData = { counters: emptyCounters };
    this.resources = { "counters": CountersResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { counters: inputs.counters };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
