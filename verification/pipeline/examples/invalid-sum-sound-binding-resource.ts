// The sound binding, and a resource needing a collection createGraph does not
// return: `Totals.instantiate` reads `input2`, and the runtime passes it the
// collections `createGraph` built, which hold only `input1`. TypeScript
// accepts the service through the bivariant parameter of
// `Resource.instantiate`; at run time `cs.input2` is undefined.
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

interface Wider extends Collections {
  readonly input2: EagerCollection<string, number>;
}

class Totals implements Resource<Wider> {
  instantiate(cs: Wider): EagerCollection<string, number> {
    return cs.input2;
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
  } = { totals: Totals };
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
