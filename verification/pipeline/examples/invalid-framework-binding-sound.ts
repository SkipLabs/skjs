// The sound binding, and a service taking more than the framework passes.
// TypeScript accepts it (method bivariance, at the implements clause and at
// the assignment to Service); at run time `extra` does not exist. The model
// refuses it: a method's parameter is contravariant.
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

interface Richer extends InputCollections {
  extra(): number;
}

class Reading implements Service<OneDef, number> {
  constructor(readonly inputs: OneDef) {}
  createGraph(inputs: Richer): number {
    return inputs.get(this.inputs.input1).value + inputs.extra();
  }
}

export function main(runtime: Runtime, defs: OneDef): number {
  const service: Service<OneDef, number> = new Reading(defs);
  return runtime.run(service);
}
