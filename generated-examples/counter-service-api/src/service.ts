import type {
  EagerCollection,
  Resource,
  ResourceClass,
  SkipService,
  Context
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  CounterId,
  CounterValue,
} from "./types.js";


export type Inputs = {
  counters: InputDefinition<CounterId, CounterValue>;
};

export type InputCollections = {
  counters: EagerCollection<CounterId, CounterValue>;
};

export type GraphCollections = {
  counters: EagerCollection<CounterId, CounterValue>;
};

export type Resources = {
  readonly "counters": ResourceClass<GraphCollections, {}>;
};



export class CountersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CounterId, CounterValue> {
    return cs.counters;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
    this.inputs = { counters: new InputDefinition<CounterId, CounterValue>([]) };
    this.resources = { "counters": CountersResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { counters: inputs.counters };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
