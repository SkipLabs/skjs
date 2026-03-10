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
  TaskId,
  TaskValue,
} from "./types.js";


export type Inputs = {
  tasks: InputDefinition<TaskId, TaskValue>;
};

export type InputCollections = {
  tasks: EagerCollection<TaskId, TaskValue>;
};

export type GraphCollections = {
  tasks: EagerCollection<TaskId, TaskValue>;
};

export type Resources = {
  readonly "tasks": ResourceClass<GraphCollections, {}>;
};


export class TasksResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TaskId, TaskValue> {
    return cs.tasks;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { tasks: new InputDefinition<TaskId, TaskValue>([]) };
    this.resources = { "tasks": TasksResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { tasks: inputs.tasks };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
