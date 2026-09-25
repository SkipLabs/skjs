// The same binding made sound. `createGraph` obtains each collection through
// the definition that declared it, so a collection exists only for a declared
// input and has that definition's types; `Inputs` is gone. The crashing
// client above cannot be written: there is no `input2` definition to ask with.
interface Collection<K, V> {
  readonly key: K;
  readonly value: V;
}
interface InputDefinition<K, V> {
  readonly initial: readonly (readonly [K, V])[];
}
interface InputCollections {
  get<K, V>(definition: InputDefinition<K, V>): Collection<K, V>;
}
interface Service<Defs, R> {
  readonly inputs: Defs;
  createGraph(inputs: InputCollections): R;
}
// `runService`: the runtime runs a service and returns its graph.
interface Runtime {
  run<Defs, R>(service: Service<Defs, R>): R;
}

interface OneDef {
  readonly input1: InputDefinition<string, number>;
}

class Reading implements Service<OneDef, number> {
  constructor(readonly inputs: OneDef) {}
  createGraph(inputs: InputCollections): number {
    return inputs.get(this.inputs.input1).value;
  }
}

export function main(runtime: Runtime, defs: OneDef): number {
  return runtime.run(new Reading(defs));
}
