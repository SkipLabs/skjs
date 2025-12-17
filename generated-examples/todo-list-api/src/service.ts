import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context
} from "@skipruntime/core";

import type {
  TodoId,
  TodoValue,
} from "./types.js";


type Inputs = {
  todos: Entry<TodoId, TodoValue>[];
};

export type InputCollections = {
  todos: EagerCollection<TodoId, TodoValue>;
};

export type GraphCollections = {
  todos: EagerCollection<TodoId, TodoValue>;
};

type Resources = {
  "todos": new (params: Json) => Resource<GraphCollections>;
};



export class TodosResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<TodoId, TodoValue> {
    return cs.todos;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyTodos: Entry<TodoId, TodoValue>[] = Array.of();
    this.initialData = { todos: emptyTodos };
    this.resources = { "todos": TodosResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { todos: inputs.todos };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
