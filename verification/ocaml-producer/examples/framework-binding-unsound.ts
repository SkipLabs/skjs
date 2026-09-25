// Today's service binding, in one file. `createGraph`'s argument type
// `Inputs` is a type parameter of its own, not tied to the declared inputs
// `Defs`, while the runtime passes one collection per declared input. So a
// service declaring only `input1` may claim `input2` too: this client
// type-checks, and at run time `inputs.input2` is undefined.
interface Collection<K, V> {
  readonly key: K;
  readonly value: V;
}
interface InputDefinition<K, V> {
  readonly initial: readonly (readonly [K, V])[];
}
interface Service<Defs, Inputs, R> {
  readonly inputs: Defs;
  createGraph(inputs: Inputs): R;
}
// `runService`: the runtime runs a service and returns its graph.
interface Runtime {
  run<Defs, Inputs, R>(service: Service<Defs, Inputs, R>): R;
}

interface OneDef {
  readonly input1: InputDefinition<string, number>;
}
interface TwoInputs {
  readonly input1: Collection<string, number>;
  readonly input2: Collection<string, number>;
}

class Crashing implements Service<OneDef, TwoInputs, number> {
  constructor(readonly inputs: OneDef) {}
  createGraph(inputs: TwoInputs): number {
    return inputs.input2.value;
  }
}

export function main(runtime: Runtime, defs: OneDef): number {
  return runtime.run(new Crashing(defs));
}
