import type {
  EagerCollection,
  Resource,
  ResourceClass,
  SkipService,
  Context
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  TodoId,
  TodoValue,
} from "./types.js";


export type Inputs = {
  todos: InputDefinition<TodoId, TodoValue>;
};

export type InputCollections = {
  todos: EagerCollection<TodoId, TodoValue>;
};

export type GraphCollections = {
  todos: EagerCollection<TodoId, TodoValue>;
};

export type Resources = {
  readonly "todos": ResourceClass<GraphCollections, {}>;
};



export class TodosResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TodoId, TodoValue> {
    return cs.todos;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
    this.inputs = {
      todos: new InputDefinition<TodoId, TodoValue>([])
    };
    this.resources = { "todos": TodosResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { todos: inputs.todos };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
