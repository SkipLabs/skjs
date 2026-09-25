// The crashing service of framework-binding-unsound.ts on the sound binding:
// it declares input1 and reads input2. Here the only way to a collection is
// through a declared definition, and there is no input2 to ask with, so the
// program is refused.
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

class Crashing implements Service<OneDef, number> {
  constructor(readonly inputs: OneDef) {}
  createGraph(inputs: InputCollections): number {
    const input2 = this.inputs.input2;
    return inputs.get(input2).value;
  }
}

export function main(runtime: Runtime, defs: OneDef): number {
  return runtime.run(new Crashing(defs));
}
