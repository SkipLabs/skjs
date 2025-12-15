import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context
} from "@skipruntime/core";

import type {
  TaskId,
  TaskValue,
} from "./types.js";


type Inputs = {
  tasks: Entry<TaskId, TaskValue>[];
};

export type InputCollections = {
  tasks: EagerCollection<TaskId, TaskValue>;
};

export type GraphCollections = {
  tasks: EagerCollection<TaskId, TaskValue>;
};

type Resources = {
  "tasks": new (params: Json) => Resource<GraphCollections>;
};


export class TasksResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TaskId, TaskValue> {
    return cs.tasks;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyTasks: Entry<TaskId, TaskValue>[] = Array.of();
    this.initialData = { tasks: emptyTasks };
    this.resources = { "tasks": TasksResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { tasks: inputs.tasks };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
