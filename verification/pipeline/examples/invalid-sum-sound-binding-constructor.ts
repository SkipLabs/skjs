// The sound binding, and a resource class whose constructor needs more than
// Json: the runtime constructs each resource with the Json the request
// carries, and `Labeled` calls its parameter's `toString`. TypeScript accepts
// it, since every Json value has `Object.prototype.toString`; but a Json
// object may own the key `toString` at any Json (`{"toString": 1}`), and
// `label()` then calls a number.
import type {
  Context,
  EagerCollection,
  ExternalService,
  InputCollections,
  Json,
  NamedEagerCollections,
  NamedInputDefinitions,
  Resource,
  ResourceClass,
  SkipService,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

import { runService, type SkipServer } from "@skipruntime/server";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}

class Labeled implements Resource<Collections> {
  constructor(readonly params: { readonly toString: () => string }) {}
  label(): string {
    return this.params.toString();
  }
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1;
  }
}

interface Inputs extends NamedInputDefinitions {
  readonly input1: InputDefinition<string, number>;
}

class Service implements SkipService<Inputs, Collections> {
  readonly inputs: Inputs = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<Collections, Json>;
  } = { labeled: Labeled };
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: InputCollections, _context: Context): Collections {
    return { input1: inputs.get(this.inputs.input1) };
  }
}

export function start(): Promise<SkipServer> {
  return runService(new Service(), {
    control_port: 3588,
    streaming_port: 3587,
  });
}
